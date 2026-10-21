-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_example13
-- name    : QAlgorithms.Papers.Independent.Next46.P22.example13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:47:00.376923+00:00
-- url     : https://prove2.me/theorems/2235ff03-46b6-452f-a525-2a8eb5980952
-- title:
--   Example 13
-- statement:
--   Let $F$ have characteristic zero and $m\ge2$, and use the concrete block algebra $L_m=\{\left(\begin{smallmatrix}C&D\\0&0\end{smallmatrix}\right):\operatorname{tr}C=0\}$, with $C,D\in M_m(F)$. Give $U(L_m)$ its primitive Hopf structure and extend the adjoint derivation action of $L_m$ on itself. For this specific action $\alpha$,
--
--   $$\alpha(\iota a)b=[a,b],\qquad U\subseteq L_m\text{ is a }U(L_m)\text{-submodule}\ \Longleftrightarrow\ U\text{ is a Lie ideal}.$$
--
--   Writing $R=\operatorname{rad}(L_m)$, no invariant semisimple subalgebra $B$ satisfies $L_m=B\oplus R$. The algebra is the same computed block algebra as in Example 12, rather than an arbitrary algebra without a Levi splitting.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 11, Example 13

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

/-- Example 13, PDF p.11: the SAME block algebra, with the extended adjoint
derivation action. Submodules are exactly ideals, and no invariant Levi splitting exists. -/
theorem example13 [CharZero F] (m : ℕ) (hm : 2 ≤ m) :
    let A := bahturinBlockLieAlgebra F m
    ∃ hopf : HopfAlgebra F (UniversalEnvelopingAlgebra F A),
      hopf.toBialgebra.toAlgebra = (inferInstance : Algebra F (UniversalEnvelopingAlgebra F A)) ∧
      (letI : Algebra F (UniversalEnvelopingAlgebra F A) := hopf.toBialgebra.toAlgebra
       letI : Module F (UniversalEnvelopingAlgebra F A) := Algebra.toModule
       letI : HopfAlgebra F (UniversalEnvelopingAlgebra F A) := hopf
       (∀ a : A,
        Coalgebra.comul (R := F) (UniversalEnvelopingAlgebra.ι F a) =
          UniversalEnvelopingAlgebra.ι F a ⊗ₜ[F] (1 : UniversalEnvelopingAlgebra F A) +
          (1 : UniversalEnvelopingAlgebra F A) ⊗ₜ[F] UniversalEnvelopingAlgebra.ι F a ∧
        Coalgebra.counit (R := F) (UniversalEnvelopingAlgebra.ι F a) = 0 ∧
        HopfAlgebra.antipode F (UniversalEnvelopingAlgebra.ι F a) =
          -UniversalEnvelopingAlgebra.ι F a) ∧
       ∃ alpha : UniversalEnvelopingAlgebra F A →ₐ[F] Module.End F A,
        (∀ a b, alpha (UniversalEnvelopingAlgebra.ι F a) b = ⁅a, b⁆) ∧ ModuleLie alpha ∧
        (∀ U : Submodule F A, ActionStable alpha U ↔ IdealSubspace U) ∧
        ¬ ∃ B : LieSubalgebra F A, Semisimple F B ∧ ActionStable alpha B.toSubmodule ∧
          IsCompl B.toSubmodule (LieAlgebra.radical F A).toSubmodule) := by sorry

end BlockExamples

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
