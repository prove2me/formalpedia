-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_local_h_bond_fusion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.local_h_bond_fusion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:46:46.413515+00:00
-- url     : https://prove2.me/theorems/6d50f10b-3f67-43f1-b044-823a036e952c
-- title:
--   §7.1 Figure 14: local fusion of one H-bond
-- statement:
--   Let $|\psi_1\rangle,|\psi_2\rangle$ be normalized qubit states, with an independent normalized $H$-bond between their respective extra virtual qubits. At each circled site apply the map $F=|0\rangle\langle00|+|1\rangle\langle11|$, explicitly renaming the even-subspace basis. In left-site/right-site order the contracted vector is
--
--   $$ (F\otimes F)|\mathrm{resource}\rangle=\tfrac12 CZ(|\psi_1\rangle\otimes|\psi_2\rangle),\qquad\| (F\otimes F)|\mathrm{resource}\rangle\|=\tfrac12. $$
--
--   Multiplication by two gives exactly the normalized $CZ$ output. This local fusion identity supplies the normalization and wire convention for the valence-bond cluster construction.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 18, §7.1 Figure 14: local fusion of one H-bond

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Fig.14, PDF pp.17–18: exact coefficient 1/2 before normalization. -/
theorem local_h_bond_fusion (psi1 psi2 : Vec Bool)
    (hpsi1 : IsState psi1) (hpsi2 : IsState psi2) :
    let v := applyRect (Matrix.kronecker fuse fuse) (fusionResource psi1 psi2)
    v = (1 / 2 : ℂ) • act (controlled pauliZ) (tensorVec psi1 psi2) ∧
    ‖v‖ = (1 / 2 : ℝ) ∧
    (2 : ℂ) • v = act (controlled pauliZ) (tensorVec psi1 psi2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
