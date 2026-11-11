-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_one_direction_moment_encoding
-- name    : QuantumFunctionalEstimation.Master.one_direction_moment_encoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:29:51.6644+00:00
-- url     : https://prove2.me/theorems/e67edddb-f035-4c40-9607-39578bff77c1
-- title:
--   Lemma 3.2 — Haar-random one-direction moment encoding
-- statement:
--   Let $D\ge2$, let $L,n$ be nonnegative integers, and let $\mu_0,\mu_1$ be arbitrary probability laws matching moments zero through $L$, supported on $[-1,D-1]\cap[-B,B]$. For independent $Z\sim\mu_b$ and Haar unit direction $u$, write $\sigma_b^{(n)}=\mathbb E[\varsigma_{Z,u}^{\otimes n}]$. With $R=2nB^2/(D-1)^2<1$,
--   $$T(\sigma_0^{(n)},\sigma_1^{(n)})\le\sqrt{\frac{R^{L+1}}{1-R}},\qquad R\le1/16\Longrightarrow T(\sigma_0^{(n)},\sigma_1^{(n)})\le4^{-L}.$$
--   Here $T(A,B)=\tfrac12\operatorname{tr}|A-B|$. Both conclusions control the same independent sampling law, which will be used inside the multi-direction construction.
--
--   **Formalization Note** Compact support makes every moment integrable. Zero copies are also included: both tensor averages are the scalar identity, so the distance is zero.
--
--   Differences from the source:
--   - encoding: independent Z and Haar u with an n-copy average → integral against their product measure after applying the published tensor power; reason: preserves independence and the same random state in all tensor factors
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), Lemma 3.2 and Definition 3.1, printed p. 14 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/451.pdf

import Definitions.Def_QuantumFunctionalEstimation_Master_Encodings
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators Matrix ComplexOrder Matrix.Norms.Elementwise

namespace QuantumFunctionalEstimation.Master

/-- Lemma 3.2, printed p.14 (PDF p.16); both conclusions. -/
theorem one_direction_moment_encoding (D : ℕ) (hD : 2 ≤ D) (L n : ℕ) (B : ℝ)
    (μ₀ μ₁ : ProbabilityMeasure ℝ)
    (hmatch : MomentMatching L μ₀ μ₁)
    (hs₀ : Supported μ₀ (Set.Icc (-1) (D - 1 : ℝ) ∩ Set.Icc (-B) B))
    (hs₁ : Supported μ₁ (Set.Icc (-1) (D - 1 : ℝ) ∩ Set.Icc (-B) B)) :
    let R : ℝ := 2 * n * B ^ 2 / (D - 1 : ℝ) ^ 2
    let T := QAlgorithms.traceDistance
      (oneAverage D (by omega) μ₀ n) (oneAverage D (by omega) μ₁ n)
    R < 1 → T ≤ Real.sqrt (R ^ (L + 1) / (1 - R)) ∧
      (R ≤ 1 / 16 → T ≤ (4 : ℝ) ^ (-(L : ℤ))) := by sorry

end QuantumFunctionalEstimation.Master
