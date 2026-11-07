-- Prove2me | Theorems.Thm_SubsetConvFPRAS_lemma_3_1
-- name    : SubsetConvFPRAS.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:41.328751+00:00
-- url     : https://prove2.me/theorems/e1ceda46-1242-4739-88b3-d6e8082e9faa
-- title:
--   Lemma 3.1 — counting from approximate conditional sampling (Jerrum–Valiant–Vazirani)
-- statement:
--   Let $m\ge1$, let $w:\{0,1\}^m\to\mathbb R_{\ge0}$, $Z=\sum_\sigma w(\sigma)$, and suppose a conditional sampler is available: for every partial assignment and every starting state compatible with it of positive weight, and every $0<\tau<1$, it returns a compatible state of positive weight whose law is within total variation $\tau$ of the conditional law, using fresh randomness. Given $\sigma_0$ with $w(\sigma_0)>0$ and $0<\varepsilon,\delta<1$, the estimator of the JVV file, run with accuracy $\tau=\varepsilon/(16m)$ and $s=\lceil C_0m^2\varepsilon^{-2}\log(2m/\delta)\rceil$ samples per coordinate, returns $\hat Z$ with
--   $$\Pr\bigl[(1-\varepsilon)Z\le\hat Z\le(1+\varepsilon)Z\bigr]\ge1-\delta,$$
--   and on every execution it makes at most $C_1m^3\varepsilon^{-2}\log(2m/\delta)$ sampler calls and at most as many additional arithmetic operations, with one evaluation of $w$, supplying a starting state to every call. The constants $C_0,C_1$ are universal.
--
--   This is the counting step of Theorem 5.1, applied to the $2n$ membership bits of a pair $(S,T)$.
--
--   Differences from the source:
--   - generalization: "one can compute Ẑ" with the stated cost → the explicit self-reduction estimator (majority bit, product of frequencies), with universal C₀, C₁; reason: the page gives no algorithm; a specific estimator with the guarantee implies the existence it asserts, and a bare existential would be trivial in Lean
--   - encoding: w nonzero → a state σ₀ with w(σ₀) > 0 is given; reason: the page gives σ₀ ∈ supp w as input, which implies w ≠ 0
--   - encoding: Pr over the algorithm's randomness → the outer measure of the bad event under the estimator's PMF, built by binding one sampler PMF per call; reason: fresh independent randomness per call
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Lemma 3.1, p.18 (citing Jerrum, Valiant, Vazirani 1986)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_JVV

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Lemma 3.1 ([JVV86]), p.18. Given a sampler for every conditional
law, the estimator `jvvEstimate` satisfies `Pr[(1-ε)Z ≤ Ẑ ≤ (1+ε)Z] ≥ 1-δ`, and on every execution uses
`Q = O(m³ ε⁻² log(2m/δ))` sampler calls, each with total variation distance `τ = ε/(16m)`, one evaluation of `w` and
`O(Q)` additional operations, and it supplies a starting state for every call.

**Formalization Note.** The page cites the estimator without writing it, so it is the explicit function `jvvRun`, with
`s = ⌈C₀ m² ε⁻² log(2m/δ)⌉` samples per coordinate. `C₀, C₁` are universal. The one evaluation of `w` is the one in
`jvvEstimate`; the starting states are the `start` fields of the run. -/
theorem lemma_3_1 :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ (w : (Fin m → Bool) → ℝ), (∀ σ, 0 ≤ w σ) →
      ∀ (samp : (Fin m → Option Bool) → (Fin m → Bool) → ℝ → PMF (Fin m → Bool)),
        IsCondSampler w samp →
      ∀ (σ₀ : Fin m → Bool), 0 < w σ₀ → ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        let s : ℕ := ⌈C₀ * (m : ℝ) ^ 2 * (ε⁻¹) ^ 2 * Real.log (2 * m / δ)⌉₊
        let D := jvvRun samp σ₀ (ε / (16 * m)) s
        let Z : ℝ := ∑ σ, w σ
        D.toOuterMeasure {st | ¬ ((1 - ε) * Z ≤ jvvEstimate w st ∧ jvvEstimate w st ≤ (1 + ε) * Z)}
            ≤ ENNReal.ofReal δ ∧
        ∀ st ∈ D.support,
          (st.samplerCalls : ℝ) ≤ C₁ * (m : ℝ) ^ 3 * (ε⁻¹) ^ 2 * Real.log (2 * m / δ) ∧
          (st.ops : ℝ) ≤ C₁ * (m : ℝ) ^ 3 * (ε⁻¹) ^ 2 * Real.log (2 * m / δ) := by sorry

end SubsetConvFPRAS
