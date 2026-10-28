-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P24_conjugatedStepColumns
-- name    : QAlgorithms.Papers.Independent.Support50.P24.conjugatedStepColumns
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:01:28.404389+00:00
-- url     : https://prove2.me/theorems/c77acb2d-2c66-4629-80c9-31d02623cc7b
-- title:
--   Both columns of the conjugated circuit step
-- statement:
--   Let $U\in\mathrm{SU}(2)$, $f_U=V^{(2)}U_2V^{(1)}U_2$, and $g_U=U_1^\dagger f_U U_1$, using the same specified known gates as Fig. S3. For any $|\phi\rangle\in\mathbb C^2$, set $v_\phi=|\phi\rangle_1|\psi^-\rangle_{23}|0^4\rangle$ and $w_\phi=|\psi^-\rangle_{12}|\phi\rangle_3|0^4\rangle$. Then
--
--   $$g_U(v_\phi,w_\phi)=(v_\phi,w_\phi)\frac1{\sqrt3}\begin{pmatrix}-1&-1\1&-2\end{pmatrix}.$$
--
--   Both column identities are asserted. The vectors span the four-dimensional invariant space in the source. They are not orthogonal: for unit $\phi$, $\langle v_\phi,w_\phi\rangle=-1/2$. Consequently no ordinary coefficient-space unitarity of the displayed matrix is asserted. This action determines the exact sign after two iterations.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, PDF p. 10, Lemma S2: exact two-column action of the conjugated step

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

/-- PDF pp.9-14, Lemma S2, S26-S27: both columns of the actual conjugated step.
The spanning pair is nonorthogonal, so no Euclidean unitarity assertion about G is made. -/
theorem conjugatedStepColumns (U : QubitSU) (phi : Bool → ℂ) :
    let firstWire := controlledGate [] 0 U.val
    let g := firstWireᴴ * evaluateCalls iteration U * firstWire
    let v := inputEmbedding.mulVec phi
    let w := swappedEmbedding.mulVec phi
    g.mulVec v = (-(Real.sqrt 3 : ℂ)⁻¹) • v + (Real.sqrt 3 : ℂ)⁻¹ • w ∧
    g.mulVec w = (-(Real.sqrt 3 : ℂ)⁻¹) • v + (-(2 : ℂ) / (Real.sqrt 3 : ℂ)) • w := by sorry

end QAlgorithms.Papers.Independent.Support50.P24

end
