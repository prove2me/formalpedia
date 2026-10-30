-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_balanced_embedding
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.balanced_embedding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:33:37.382356+00:00
-- url     : https://prove2.me/theorems/aa5901c8-eead-414a-b157-3b1b1c6e5cb5
-- title:
--   §II Eqs.(21)–(23): balanced two-qubit three-feature embedding
-- statement:
--   For real $x=(x_1,x_2,x_3)$, put $E(x)=\exp[-\frac i2(x_1X\otimes X+x_2Y\otimes Y+x_3Z\otimes Z)]$. For distinct Pauli axes $A,B$, let $H_{AB}=\exp[-i\pi(A+B)/(2\sqrt2)]$. If $\tau_{AB}$ exchanges the corresponding two feature coordinates, then
--   $$E(\tau_{AB}x)=(H_{AB}\otimes H_{AB})E(x)(H_{AB}\otimes H_{AB})^\dagger.$$
--   Each $H_{AB}$ is unitary. The three transposition identities implement the feature permutations by conjugation. The printed phase is preserved; no ordinary representation law for the three chosen lifts is asserted.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 5, §II Eqs.(21)–(23): balanced two-qubit three-feature embedding

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

/-- PDF p.5, Eqs.(21)–(23): transposition conjugations with the printed exponential phase.
Only the induced adjoint actions, rather than these chosen lifts, realize the permutations. -/
theorem balanced_embedding (x : Fin 3 → ℝ) :
    (∀ a b : Fin 3, a ≠ b → balancedEncoding (featurePullback (Equiv.swap a b) x) =
      conjugate (axisHadamard a b ⊗ₖ axisHadamard a b) (balancedEncoding x)) ∧
    (∀ a b : Fin 3, a ≠ b → axisHadamard a b ∈ Matrix.unitaryGroup Bool ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
