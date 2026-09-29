-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_tensor_indBot
-- name    : Rep.isZero_tateCohomology_tensor_indBot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/8880b680-2343-5c9d-8d7e-6cdd1dd08876
-- title:
--   Tate cohomology of A ⊗ Ind₁^G B vanishes
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group, and let $A$ and $B$ be $k$-linear representations of $G$ (objects of `Rep k G`), with $k$, $G$ and the representations in a single universe. Write `B.indBot` for the representation obtained from $B$ by restricting along the inclusion of the trivial subgroup $\bot \le G$ and then inducing back along that same inclusion, i.e. $\mathrm{Ind}_{\bot}^{G}\mathrm{Res}_{\bot}^{G} B$. For every integer $q$, the object $(A \otimes B_{*}).\mathrm{tateCohomology}\,q$ of `ModuleCat k`, where $B_* =$ `B.indBot` and $\otimes$ is the monoidal product of `Rep k G`, is a zero object (`IsZero`, i.e. simultaneously initial and terminal). Here the Tate cohomology of a representation $M$ in degree $q$ is, by definition, group cohomology $H^{n+1}(G, M)$ when $q = n+1 > 0$; the quotient of the $G$-invariants of $M$ by the range of the norm map $\rho.\mathrm{normBar}$ when $q = 0$; the kernel of that norm map when $q = -1$; and group homology $H_{n+1}(G, M)$ when $q = -(n+2)$.
--
--   This is the standard acyclicity of a tensor product one factor of which is induced from the trivial subgroup (a relatively injective, or cohomologically trivial, module), in the form needed for dimension shifting in the second tensor variable. It is used in the construction and verification of the properties of the Tate cup product, being cited by the associativity, commutativity and comparison lemmas for that product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_tensor_indBot.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.isZero_tateCohomology_tensor_indBot {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A B : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((A ⊗ B.indBot).tateCohomology q) := by sorry
