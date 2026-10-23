-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
-- name    : QAlgorithms.Papers.Independent.Gap48.P20.strongSubadditivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:09:38.267054+00:00
-- url     : https://prove2.me/theorems/bb70c65c-bbe8-423b-bc1f-35c413262201
-- title:
--   Finite-dimensional strong subadditivity in bits
-- statement:
--   Let $C,R,B$ be nonzero finite-dimensional registers and let $\rho^{CRB}$ be any positive semidefinite matrix of trace one. All reduced states are obtained by actual partial traces, and $H$ denotes von Neumann entropy with logarithm base two. Then
--   $$
--   H(CB)_\rho+H(RB)_\rho-H(B)_\rho-H(CRB)_\rho\ge0.
--   $$
--   Equivalently $I(C;R\mid B)_\rho\ge0$. The state may be mixed, singular, or supported on a one-dimensional subspace.
--
--   This is the finite-dimensional strong-subadditivity corollary discussed operationally in the paper. Nonnegativity of conditional mutual information is not assumed.
-- source:
--   The operational meaning of quantum conditional information, arXiv:quant-ph/0612050v2, PDF p. 4, strong-subadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P20

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1,4: the finite-matrix strong-subadditivity corollary, in bits.
No nonnegativity assumption is made, and rho can be any mixed density matrix. -/
theorem strongSubadditivity {C R B : Type*}
    [Fintype C] [Fintype R] [Fintype B]
    [Nonempty C] [Nonempty R] [Nonempty B]
    (rho : Matrix (C × (R × B)) (C × (R × B)) ℂ)
    (hrho : IsDensityMatrix rho) :
    0 ≤ subsystemEntropy rho (fun p => (p.1, p.2.2)) (fun p => p.2.1) +
      subsystemEntropy rho (fun p => p.2) (fun p => p.1) -
      subsystemEntropy rho (fun p => p.2.2) (fun p => (p.1, p.2.1)) -
      vnEntropy rho := by sorry

end QAlgorithms.Papers.Independent.Gap48.P20

end
