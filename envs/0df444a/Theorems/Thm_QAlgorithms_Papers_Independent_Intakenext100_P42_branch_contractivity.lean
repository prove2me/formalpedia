-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_branch_contractivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.branch_contractivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:41:34.179976+00:00
-- url     : https://prove2.me/theorems/0dd59641-0705-4262-a1ae-9bc50c31ea91
-- title:
--   Theorem 2: summed branch contractivity
-- statement:
--   All registers are finite and nonempty; all input density matrices are positive semidefinite with trace one.
--
--   Under F2, F3, F5a, and unit-vector F5b on the coherent positive subnormalized domain, let $V_i$ be a finite Kraus family with $\sum_iV_i^\dagger V_i=I$. For density matrices $\sigma,\rho$, set $\sigma_i=V_i\sigma V_i^\dagger$ and $\rho_i=V_i\rho V_i^\dagger$. Then
--
--   $$\sum_iD(\sigma_i\Vert\rho_i)\le D(\sigma\Vert\rho).$$
--
--   The family need not be local; the inequality retains branch information.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 10, Theorem 2: summed branch contractivity

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

/-- Theorem 2, PDF p.10: summed subnormalized branch contractivity.
Both states use forward conjugation; completeness is inherited from the setup. -/
theorem branch_contractivity (D : DistanceFamily) (h2 : UnitaryInvariantDistance D) (h3 : F3 D true)
    (h5a : F5a D) (h5b : F5b D)
    {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (V : K → Matrix J I ℂ) (hV : IsKrausFamily V)
    (sigma rho : Matrix I I ℂ) (hsigma : IsDensityMatrix sigma) (hrho : IsDensityMatrix rho) :
    (∑ k, D (rectangularKrausBranch V sigma k) (rectangularKrausBranch V rho k)) ≤ D sigma rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
