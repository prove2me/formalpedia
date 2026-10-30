-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_dimension_achievability
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.dimension_achievability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:18:55.545554+00:00
-- url     : https://prove2.me/theorems/d6098f18-f6ba-4d47-bc75-f9794a412ba1
-- title:
--   Theorem 1.5: explicit dimension-dependent achievability
-- statement:
--   For $d\ge1$, define the explicit coefficient from the proof by
--   $$A(d)=\frac{d-1}{2}\left(\sqrt{\frac{d+1}{2}}+1\right)^2 d\left(\frac{d(d-1)}{\sqrt2}+\sqrt{d(d-1)}+\sqrt2\right).$$
--   For each fixed $d$, there are $C_d>0$ and $N_0\ge1$ such that
--   $$F_d^*(N)\ge1-\frac{A(d)}{N^2}-\frac{C_d}{N^3}\qquad(N\ge N_0).$$
--   Moreover, there are constants $K>0,d_0\ge2$, uniform in $d\ge d_0$, with $|A(d)-d^5/(4\sqrt2)|\le Kd^{9/2}$. This makes both asymptotic quantifier orders explicit.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 6, Theorem 1.5: explicit dimension-dependent achievability

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Theorem 1.5, PDF p.6, resolved by the explicit coefficient in its proof, p.47.
The N remainder is dimension-dependent; the d^(9/2) estimate is uniform in large d. -/
theorem dimension_achievability :
    (∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0,
      1 - dimensionCoefficient d / (N : ℝ)^2 - C/(N : ℝ)^3 ≤ pbtOptimalFidelity d N) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ d0 : ℕ, 2 ≤ d0 ∧ ∀ d ≥ d0,
      |dimensionCoefficient d - (d : ℝ)^5/(4*Real.sqrt 2)| ≤
        K * Real.rpow (d : ℝ) ((9 : ℝ)/2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
