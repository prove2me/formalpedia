-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_example12
-- name    : QAlgorithms.Papers.Independent.Next46.P22.example12
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:45:32.203339+00:00
-- url     : https://prove2.me/theorems/b9049698-9235-41d8-b2e4-d5b02e6988bd
-- title:
--   Example 12 (Yuri Bahturin)
-- statement:
--   Let $F$ have characteristic zero and $m\ge2$. Define the concrete matrix Lie algebra and its off-diagonal subspace by
--
--   $$L_m=\left\{\begin{pmatrix}C&D\\0&0\end{pmatrix}:C,D\in M_m(F),\ \operatorname{tr}C=0\right\},\qquad R=\left\{\begin{pmatrix}0&D\\0&0\end{pmatrix}:D\in M_m(F)\right\}.$$
--
--   Then $R$ is both the solvable and nilpotent radical. The map $\phi(C,D)=(C,C+D)$ is a Lie automorphism of infinite order. Its powers define the infinite cyclic action, whose linear extension makes $L_m$ an $F\mathbb Z$-module Lie algebra and preserves $R$. There is no invariant semisimple subalgebra $B$ with $L_m=B\oplus R$. The model is the Lie span of the displayed matrices, with equality to that exact set included in the theorem.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 10, Example 12 (Yuri Bahturin)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

section BlockExamples

attribute [local instance] LieRing.ofAssociativeRing

/-- Example 12 (Yuri Bahturin), PDF pp.10–11: exact displayed block algebra,
actual radicals, actual shift automorphism, infinite cyclic action, and failure
of every invariant semisimple complement. Characteristic zero and m≥2 retained. -/
theorem example12 [CharZero F] (m : ℕ) (hm : 2 ≤ m) :
    (∀ X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F,
      X ∈ bahturinBlockLieAlgebra F m ↔ ∃ C D : Matrix (Fin m) (Fin m) F,
        Matrix.trace C = 0 ∧ X = blockElement m C D) ∧
    (LieAlgebra.radical F (bahturinBlockLieAlgebra F m)).toSubmodule = blockRadical F m ∧
    (lieNilpotentRadical F (bahturinBlockLieAlgebra F m)).toSubmodule = blockRadical F m ∧
    ∃ phi : bahturinBlockLieAlgebra F m ≃ₗ⁅F⁆ bahturinBlockLieAlgebra F m,
      (∀ a, (phi a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) = blockShift m a) ∧
      Function.Injective (fun n : ℤ =>
        (phi.toLinearEquiv.toEquiv : Equiv.Perm (bahturinBlockLieAlgebra F m)) ^ n) ∧
      ∃ alpha : MonoidAlgebra F (Multiplicative ℤ) →ₐ[F] Module.End F (bahturinBlockLieAlgebra F m),
        (∀ n : ℤ, ∀ a, alpha (MonoidAlgebra.single (Multiplicative.ofAdd n) 1) a =
          ((phi.toLinearEquiv.toEquiv : Equiv.Perm (bahturinBlockLieAlgebra F m)) ^ n) a) ∧
        ModuleLie alpha ∧ ActionStable alpha (blockRadical F m) ∧
        ¬ ∃ B : LieSubalgebra F (bahturinBlockLieAlgebra F m), Semisimple F B ∧
          ActionStable alpha B.toSubmodule ∧ IsCompl B.toSubmodule (blockRadical F m) := by sorry

end BlockExamples

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
