-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_pinching_contractivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.pinching_contractivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:40:40.016029+00:00
-- url     : https://prove2.me/theorems/84112a93-f209-4a84-a1dd-3b0b177acc70
-- title:
--   Corollary to Theorem 1: pinching
-- statement:
--   All registers are finite and nonempty; all input density matrices are positive semidefinite with trace one.
--
--   Let $D$ satisfy F2, F3, unit-vector F5b, and block additivity F5a on the positive subnormalized domain. Let $P_i$ be a finite complete family of pairwise orthogonal Hermitian projectors, and let $\sigma,\rho$ be density matrices. Then
--
--   $$\sum_iD(P_i\sigma P_i\Vert P_i\rho P_i)\le D(\sigma\Vert\rho).$$
--
--   This is the summed-block consequence of pinching contractivity, including zero blocks.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 10, Corollary to Theorem 1: pinching

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary, PDF p.10, Eq.(15): the right-hand projectors occur in BOTH blocks. -/
theorem pinching_contractivity (D : DistanceFamily) (h2 : UnitaryInvariantDistance D) (h3 : F3 D)
    (h5a : F5a D) (h5b : F5b D)
    {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [Nonempty I]
    (P : K → Matrix I I ℂ) (hP : CompleteProjectors P)
    (sigma rho : Matrix I I ℂ) (hsigma : IsDensityMatrix sigma) (hrho : IsDensityMatrix rho) :
    (∑ k, D (P k * sigma * P k) (P k * rho * P k)) ≤ D sigma rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
