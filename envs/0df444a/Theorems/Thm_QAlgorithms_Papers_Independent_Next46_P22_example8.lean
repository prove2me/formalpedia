-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_example8
-- name    : QAlgorithms.Papers.Independent.Next46.P22.example8
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:37:45.480295+00:00
-- url     : https://prove2.me/theorems/ade906a3-5b87-42fd-8d92-4ceb98209a71
-- title:
--   Example 8
-- statement:
--   Let $F$ be any field, $L$ an $F$-Lie algebra, $G$ any group, and $g\mapsto A_g$ a fixed homomorphism from $G$ to the group of $F$-linear Lie automorphisms of $L$. Its linear extension $\alpha:FG\to\operatorname{End}_F(L)$ is an algebra homomorphism and makes $L$ an $FG$-module Lie algebra:
--
--   $$\alpha(g)a=A_g(a),\qquad h[a,b]=\sum[h_1a,h_2b]\quad(h\in FG).$$
--
--   Here $\Delta(h)=\sum h_1\otimes h_2$ is the standard group-algebra comultiplication. The fixed generator action pins the extension; no independent unrelated action is chosen.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 5, Example 8

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Example 8, PDF p.5: linear extension of the fixed G-action by Lie automorphisms.
The two equations express exactly that act is a group homomorphism. -/
theorem example8 {G : Type*} [Group G] (act : G → L ≃ₗ⁅F⁆ L)
    (act_one : ∀ a, act 1 a = a)
    (act_mul : ∀ g h a, act (g * h) a = act g (act h a)) :
    ∃ alpha : MonoidAlgebra F G →ₐ[F] Module.End F L,
      (∀ g a, alpha (MonoidAlgebra.single g 1) a = act g a) ∧ ModuleLie alpha := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
