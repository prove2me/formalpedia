-- Prove2me | Theorems.Thm_Rep_tateMap_comp
-- name    : Rep.tateMap_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/385eafed-ffd8-5bee-8dcb-575177c787be
-- title:
--   Functoriality of Tate cohomology: compatibility with composition
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $A$, $B$, $C$ be $k$-linear representations of $G$ (objects of `Rep k G`). Given morphisms $\varphi : A \to B$ and $\psi : B \to C$ of representations and an integer $n$, the map induced on Tate cohomology in degree $n$ by the composite $\varphi$ followed by $\psi$ equals the composite of the induced maps, $\mathrm{tateMap}(\psi \circ \varphi, n) = \mathrm{tateMap}(\psi, n) \circ \mathrm{tateMap}(\varphi, n)$. Here [`Rep.tateCohomology`](def/GroupCohomology_TateCohomology.html#L140) and [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17) are defined by cases on $n$: for $n = m+1 \ge 1$ they are group cohomology $H^{m+1}(G, -)$ and the map `groupCohomology.map` induced by the identity of $G$ and the given morphism; for $n = -(m+2) \le -2$ they are group homology $H_{m+1}(G, -)$ and `groupHomology.map` likewise; for $n = 0$ the group is the quotient of the invariants by the range of the norm map `normBar`, with the morphism induced by the map on invariants; and for $n = -1$ it is the kernel of `normBar` inside the coinvariants, with the morphism induced by the map on coinvariants. The asserted identity is one equation of morphisms of $k$-modules for each fixed $n$, not the functoriality of a single functor on $\mathbb{Z}$-graded objects.
--
--   This is the composition half of the functoriality of the Tate cohomology groups $\hat H^n(G, -)$ in the coefficient representation, for all $n \in \mathbb{Z}$ simultaneously. It is used in the development of the Tate cup product and of the Tate–Nakayama pairing, for instance by [`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2) and [`Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq`](thm.html#Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_tateMap_comp.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.tateMap_comp {k G : Type u} [CommRing k] [Group G] [Fintype G] {A B C : Rep.{u} k G}
    (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℤ) :
    Rep.tateMap (φ ≫ ψ) n = Rep.tateMap φ n ≫ Rep.tateMap ψ n := by sorry
