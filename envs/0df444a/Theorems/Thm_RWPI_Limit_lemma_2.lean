-- Prove2me | Theorems.Thm_RWPI_Limit_lemma_2
-- name    : RWPI.Limit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:10:40.278977+00:00
-- url     : https://prove2.me/theorems/8ad51686-b57d-4e4d-b239-76bd6e3d4b67
-- title:
--   Lemma 2 — localisation: $\mathbb P(\sup_{\|\zeta\|_p\ge b}\{-\zeta^T H_n - M_n(\zeta)\} > 0) \le \varepsilon$ for $n \ge n_0$
-- statement:
--   Let $W, W_1, W_2, \dots$ be i.i.d. random vectors in $\mathbb R^m$, let $h : \mathbb R^m \times \mathbb R^l \to \mathbb R^r$ and $\theta_* \in \mathbb R^l$. Assume:
--
--   1. (A1) $\rho \ge 1$, $q \in (1, \infty]$ and $p$ is the conjugate exponent, $1/p + 1/q = 1$;
--   2. (A2) $\mathbb E[h(W, \theta_*)] = \mathbf 0$ and $\mathbb E\|h(W, \theta_*)\|_2^2 < \infty$;
--   3. (A3) $h(\cdot, \theta_*)$ is continuously differentiable, with derivative $Dh = D_w h(\cdot, \theta_*)$;
--   4. (A4) for every $\zeta \in \mathbb R^r$ with $\zeta \ne 0$, $\mathbb P(\|\zeta^T D_w h(W, \theta_*)\|_p > 0) > 0$.
--
--   Let $H_n$ and $M_n$ be the quantities of (31)–(32) computed from $W_1, \dots, W_n$. Then for every $\varepsilon > 0$ there exist $n_0 > 0$ and $b \in (0, \infty)$ such that, for all $n \ge n_0$,
--
--   $$
--   \mathbb P\Big( \sup_{\|\zeta\|_p \ge b} \big\{ -\zeta^T H_n - M_n(\zeta) \big\} > 0 \Big) \le \varepsilon .
--   $$
--
--   Since the supremum over all $\zeta$ is at least $0$ (take $\zeta = 0$), the lemma shows that with high probability the representation (31) of $n^{\rho/2}R_n(\theta_*)$ is determined by a fixed compact set of multipliers $\zeta$; this localisation is what makes the continuous-mapping argument of Theorem 3 possible.
--
--   **Formalization Note.** The samples are $W_0, W_1, \dots$ (indexed from $0$), independent and identically distributed with the law of $W_0$, and the event "the supremum is positive" is written as "some $\zeta$ with $\|\zeta\|_p \ge b$ has a positive value". The probability is the outer measure of that event, so no measurability is assumed. The page lists A2)–A4); A1) and the i.i.d. sampling are the paper's standing setting and are stated explicitly. The paper allows $q \ge 1$ in A1) but works with $q \in (1,\infty]$ in (17) and in the proof (p. 33, "Recall that $q > 1$"); the latter is used.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 32, App. A.3, Lemma 2 (proof pp. 33–34)

import Mathlib
import Definitions.Def_RWPI_Limit_dualRep
import Definitions.Def_RWPI_Limit_rowNorm

open MeasureTheory ProbabilityTheory

namespace RWPI.Limit

/-- Lemma 2 (Blanchet, Kang & Murthy, arXiv:1610.05627v4, App. A.3, p. 32): localisation of the
dual representation (31). `W_0, W_1, …` are i.i.d. random vectors in `ℝ^m`; `H_n`, `M_n` are
evaluated at the first `n` samples. Under A1) (with `q ∈ (1, ∞]`, `1/p + 1/q = 1`, `ρ ≥ 1`) and
A2)–A4), for every `ε > 0` there are `n₀ > 0` and `b ∈ (0, ∞)` with
`P( sup_{‖ζ‖_p ≥ b} { −ζ^T H_n − M_n(ζ) } > 0 ) ≤ ε` for all `n ≥ n₀`. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m l r : ℕ} (W : ℕ → Ω → (Fin m → ℝ)) (hWmeas : ∀ i, Measurable (W i))
    (hindep : iIndepFun W μ) (hident : ∀ i, IdentDistrib (W i) (W 0) μ μ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q)
    -- A2)
    (hint : Integrable (fun ω => h (W 0 ω) θs) μ) (hmean : ∫ ω, h (W 0 ω) θs ∂μ = 0)
    (hL2 : MemLp (fun ω => h (W 0 ω) θs) 2 μ)
    -- A3)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    -- A4)
    (hA4 : ∀ ζ : Fin r → ℝ, ζ ≠ 0 → 0 < μ {ω | 0 < rowNorm p h θs ζ (W 0 ω)}) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, n₀ ≤ n →
      μ {ω | ∃ ζ : Fin r → ℝ, b ≤ ‖WithLp.toLp p ζ‖ ∧
        (0 : EReal) < (((-(ζ ⬝ᵥ Hn h θs (fun i : Fin n => W i ω))) : ℝ) : EReal)
          - Mn q ρ h θs (fun i : Fin n => W i ω) ζ} ≤ ENNReal.ofReal ε := by sorry

end RWPI.Limit
