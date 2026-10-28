-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_selfFidelityIdealChannel
-- name    : QAlgorithms.Papers.Independent.Support50.P31.selfFidelityIdealChannel
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:29:03.522619+00:00
-- url     : https://prove2.me/theorems/0e57692a-4642-4951-a198-1d3589f719f5
-- title:
--   Maximal survival probability is stable under an ideal ancilla
-- statement:
--   Let $\Phi$ be a completely positive trace-preserving endomorphism on the operators of a nonzero finite-dimensional complex Hilbert space $H$. Define its maximal survival probability by
--   $$
--   \nu_\flat(\Phi)
--   =\sup_{\|\psi\|=1}\langle\psi,\Phi(|\psi\rangle\langle\psi|)\psi\rangle .
--   $$
--   For the identity channel on any nonzero finite-dimensional ancillary space $A$,
--   $$
--   \nu_\flat(\operatorname{Id}_A\otimes\Phi)=\nu_\flat(\Phi).
--   $$
--   The joint supremum allows all unit vectors in $A\otimes H$, including entangled vectors. Equal input and output algebras are part of the endomorphism assumption. This is maximal survival probability, rather than minimal, average, or entanglement fidelity.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 6, §3, equation (13): stability of maximal self-fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF pp.6–7, (13): stability of maximal survival probability, for an endomorphism.
This is not a minimal or average gate fidelity. Ideal register is written first. -/
theorem selfFidelityIdealChannel {I J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J] (Phi : Superop I I) (hPhi : IsChannel Phi) :
    nuFlat (idTensorSuperop (R := J) Phi) = nuFlat Phi := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
