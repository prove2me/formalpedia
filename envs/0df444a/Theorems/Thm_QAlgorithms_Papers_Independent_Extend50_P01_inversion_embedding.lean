-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_inversion_embedding
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.inversion_embedding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:36:31.789869+00:00
-- url     : https://prove2.me/theorems/e0856b45-404d-4768-9c64-3072f2866755
-- title:
--   §II Eqs.(35)–(39): two-qubit inversion identity
-- statement:
--   For real $x\in\mathbb R^3$, define $E_2(x)=\exp[-\frac i2(x_1X+x_2Y+x_3Z)\otimes X]$. Then
--   $$E_2(-x)=(I\otimes Z)E_2(x)(I\otimes Z),\qquad (I\otimes Z)^2=I.$$
--   Thus spatial inversion alone has the specified ordinary order-two implementation on two qubits. This identity requires no ordinary representation of the full orthogonal group.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 7, §II Eqs.(35)–(39): two-qubit inversion identity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01

noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P01

attribute [local instance] Classical.propDecidable Classical.decEq

-- PDF pp.3,8: reuse the accepted operator type, exp(-itH), and A X A†.
-- Notation specializes the imported interfaces without introducing duplicate declarations.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "evolve" => QAlgorithms.Papers.Independent.Information100.P32.evolution

local notation "conjugate" => QAlgorithms.conjSuperop

-- PDF pp.3,10–11: the imported quadratic form is Re(psi† A psi).

local notation "expectation" => QAlgorithms.Papers.Independent.Information100.P21.quad

-- PDF pp.5,16–19: accepted active-wire operator, with identities on all spectators.

local notation "onWire" => QAlgorithms.Papers.Independent.Advance50.P49.onWire

-- PDF p.5: the imported phase-free Pauli tensor uses 0=I,1=X,2=Y,3=Z.

local notation "pauliWord" => QAlgorithms.Papers.Independent.Gap48.P33.pauliWord

/-- PDF p.7, Eqs.(35)–(39): inversion alone, without assuming an O(3) lift. -/
theorem inversion_embedding (x : Fin 3 → ℝ) :
    inversionEncoding (-x) = (1 ⊗ₖ pauliZ) * inversionEncoding x * (1 ⊗ₖ pauliZ) ∧
    (1 ⊗ₖ pauliZ : Matrix (Bool × Bool) (Bool × Bool) ℂ) ^ 2 = 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
