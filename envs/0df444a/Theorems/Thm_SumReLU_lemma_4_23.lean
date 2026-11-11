-- Prove2me | Theorems.Thm_SumReLU_lemma_4_23
-- name    : SumReLU.lemma_4_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:34.343706+00:00
-- url     : https://prove2.me/theorems/b87547ea-c17b-46dc-82f2-5e8b23d95896
-- title:
--   Lemma 4.23 — the covariance of $S_t(I)$ is at most $k^22^{O(t)}/\hat\sigma_t^2$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $d,k\ge1$, let $f(x)=\sum_i\beta_i\sigma(w_i\cdot x)$ with $\beta_i\in[0,1]$ and $\|w_i\|_2=1$, and let $(x,z)\sim N(0,I_d)\otimes N(0,I_d)$, $y=f(x)$, $I=(x,y,z)$. For every even $t\ge2$, the tensor $S_t(I)=\frac{y}{\hat\sigma_t\sqrt{t!}}\mathrm{Re}((x+iz)^{\otimes t})$ satisfies, for every complex tensor $W$ of order $t$ with $\|W\|_F=1$,
--   $$
--   \mathbb E_I\Big[\big|\big\langle S_t(I)-\mathbb E_I[S_t(I)],\,W\big\rangle\big|^2\Big]\le\frac{k^2\,2^{Ct}}{\hat\sigma_t^2},
--   $$
--   and the integrand is integrable.
--
--   This is the covariance input that lets the implicit tensor computation of [DK25] recover the compressor from polynomially many samples.
--
--   Differences from the source:
--   - encoding: $I=(x,y,z)\sim D\otimes N(0,I_d)$ → $(x,z)\sim N(0,I_d)\otimes N(0,I_d)$ with $y=f(x)$; reason: $y$ is a function of $x$
--   - encoding: $2^{O(t)}$ → $2^{Ct}$ with one absolute constant $C$ fixed before $d,k,\beta,w,t,W$; reason: big-O convention; a multiplicative constant is absorbed into the exponent since $t\ge2$
--   - encoding: $\sup_{\|W\|_F=1}\mathbb E[\cdots]\le V$ → for every $W$ with $\|W\|_F=1$: the integrand is integrable and its integral is at most the bound; reason: a supremum bound is a bound for every $W$; integrability keeps the integral from being a junk $0$
--   - reading: $t$ → every even $t\ge2$; reason: $S_t$ is defined for even $t\in\mathbb Z_+$ (Lemma 4.17)
--   - generalization: Section 4.3's standing assumption $k\le d$ (Remark 4.12, p.34: "Throughout this section, we assume without loss of generality that $k\le d$") → no relation between $d$ and $k$; reason: the bound does not depend on it (the lemma's statement involves only the law of the projections of the probe or of $(x,z)$, not the ambient dimension); the statement specializes to $k\le d$
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.23, p.38 (PDF p.40); Lemma 4.17, Equation (20), p.36 (PDF p.38)

import Mathlib
import Definitions.Def_SumReLU_reluSum
import Definitions.Def_SumReLU_reluHermite
import Definitions.Def_SumReLU_CTensor
import Definitions.Def_SumReLU_Stensor

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **Lemma 4.23** (covariance bound for the moment STC `S_t`).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.23, p.38 (PDF p.40): "Let D be a Gaussian sum of k ReLUs, and let z ∼ N(0, I_d). Let
I = (x, y, z) and denote the distribution of I by D(I) = D ⊗ N(0, I_d). Let S_t(I) be the output of
the STC circuit defined in Lemma 4.17, Equation (20). Then the covariance of S_t(I) is bounded by
sup_{‖W‖_F=1} E_{I∼D(I)}[|⟨S_t(I) − E_{I∼D}[S_t(I)], W⟩|²] ≤ V_{S_t} := k² 2^{O(t)}/σ̂_t²."
(20), p.36 (PDF p.38): "S_t(I) = S_t(x, y, z) := (y/(σ̂_t √(t!))) Re((x + iz)^{⊗t})", for even t ∈ ℤ₊.

**Formalization Note.**
* `I = (x, f(x), z)` with `(x, z) ∼ N(0, I_d) ⊗ N(0, I_d)`; `S_t` is a real tensor, viewed in
  `(ℂᵈ)^{⊗t}`; the mean is entrywise. The supremum over `‖W‖_F = 1` is stated for every complex
  `W` with `‖W‖_F = 1`.
* `2^{O(t)}`: one absolute constant `C`, chosen before `d, k, β, w, t, W`, with the bound
  `k² 2^{Ct}/σ̂_t²` (a multiplicative constant is absorbed into the exponent since `t ≥ 2`).
* Section 4.3's standing assumption `k ≤ d` (Remark 4.12, p.34, PDF p.36) is not imposed; the bound
  does not depend on it, and the statement specializes to `k ≤ d`.
* The integrability of the integrand is part of the conclusion (no junk-`0` integral). -/
theorem lemma_4_23 :
    ∃ C : ℝ, ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
      ∀ (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)), InClass β w →
      ∀ t : ℕ, Even t → 2 ≤ t → ∀ W : CTensor d t, frob W = 1 →
        let μ := (stdGaussian (EuclideanSpace ℝ (Fin d))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin d)))
        let S : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → CTensor d t :=
          fun xz J => ((Stensor t xz.1 (reluSum β w xz.1) xz.2 J : ℝ) : ℂ)
        let mean : CTensor d t := fun J => ∫ xz, S xz J ∂μ
        Integrable (fun xz => ‖cinner (S xz - mean) W‖ ^ 2) μ ∧
          ∫ xz, ‖cinner (S xz - mean) W‖ ^ 2 ∂μ ≤
            (k : ℝ) ^ 2 * (2 : ℝ) ^ (C * t) / reluHermite t ^ 2 := by sorry

end SumReLU
