-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_ihom_indBot
-- name    : Rep.isZero_tateCohomology_ihom_indBot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/92fda4bb-de21-5a13-869d-559d88d6a43f
-- title:
--   Tate-acyclicity of Hom(Ind₁^G A, W)
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group (both in the same universe), let $A$ and $W$ be $k$-linear representations of $G$, and let $q$ be an integer. Write $A_* =$ `A.indBot` for the representation obtained by restricting $A$ along the inclusion of the trivial subgroup $\bot \le G$ and then inducing back along that inclusion, so that $A_*$ has underlying module $k[G]\otimes_k A$ with $G$ acting by translation on the group coordinate alone, the generators satisfying $\rho(g)(\,h\otimes a\,) = (hg^{-1})\otimes a$. Let $(\mathrm{ihom}\ A_*).obj\ W$ be the internal hom of the monoidal category of representations, i.e. the $k$-module of $k$-linear maps $A_* \to W$ with the conjugation action of $G$. The assertion is that the degree-$q$ Tate cohomology of this representation is a zero object of `ModuleCat k`; here Tate cohomology is group cohomology $H^{n+1}$ in degrees $q = n+1 \ge 1$, the invariants modulo the image of the norm map in degree $0$, the kernel of the norm map in degree $-1$, and group homology $H_{n+1}$ in degrees $q = -(n+2) \le -2$.
--
--   This is the Tate-acyclicity of the internal hom out of a module induced from the trivial subgroup: such induced modules are cohomologically trivial, and the statement records that the property persists after passing to $\operatorname{Hom}(A_*, W)$, by an untwisting isomorphism $\operatorname{Hom}(A_*, W) \cong \operatorname{Hom}(A, W)_*$ together with [`Rep.isZero_tateCohomology_indBot`](thm.html#Rep.isZero_tateCohomology_indBot). It is used in the treatment of the Tate cup product and of the duality pairing in the dual variable, where it makes the connecting maps of a dimension shift bijective; it is cited by [`Rep.IsTateCupProduct.cupEv_characterDual_eq_zero`](thm.html#Rep.IsTateCupProduct.cupEv_characterDual_eq_zero) and [`Rep.IsTateCupProduct.injective_cupEv_characterDual`](thm.html#Rep.IsTateCupProduct.injective_cupEv_characterDual).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_ihom_indBot.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.isZero_tateCohomology_ihom_indBot {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A W : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom A.indBot).obj W).tateCohomology q) := by sorry
