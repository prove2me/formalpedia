-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_example3
-- name    : QAlgorithms.Papers.Independent.Next46.P22.example3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:35:58.115139+00:00
-- url     : https://prove2.me/theorems/131c0fd2-a8b6-45e3-a994-2b808dc5da11
-- title:
--   Example 3
-- statement:
--   Let $F$ be any field and $G$ any group. In the group algebra $FG$, identify $g\in G$ with its basis element. The standard Hopf structure and coefficient-at-identity functional $t$ satisfy
--
--   $$\Delta(g)=g\otimes g,\quad \varepsilon(g)=1,\quad \mathcal S(g)=g^{-1},\qquad t(g)=\begin{cases}1&g=1,\\0&g\ne1.\end{cases}$$
--
--   The functional $t:FG\to F$ is a left integral, is ad-invariant, and satisfies $t(1)=1$. No finiteness condition on $G$ or characteristic restriction on $F$ is required. This supplies averaging for arbitrary group gradings.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 3, Example 3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Example 3, PDF p.3: arbitrary G and F, with the specified Hopf formulas
and coefficient-at-identity normalized ad-invariant left integral. -/
theorem example3 {G : Type*} [Group G] :
    (∀ g : G,
      Coalgebra.comul (R := F) (MonoidAlgebra.single g (1 : F)) =
        MonoidAlgebra.single g 1 ⊗ₜ[F] MonoidAlgebra.single g 1 ∧
      Coalgebra.counit (R := F) (MonoidAlgebra.single g (1 : F)) = 1 ∧
      HopfAlgebra.antipode F (MonoidAlgebra.single g (1 : F)) = MonoidAlgebra.single g⁻¹ 1) ∧
    NormalizedAdIntegral (identityCoefficient (F := F) (G := G)) ∧
    ∀ g : G, identityCoefficient (MonoidAlgebra.single g (1 : F)) = if g = 1 then 1 else 0 := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
