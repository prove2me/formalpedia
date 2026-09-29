-- Prove2me | Theorems.Thm_Rep_exists_hom_dimShiftDownObj_trivial_leftRegular
-- name    : Rep.exists_hom_dimShiftDownObj_trivial_leftRegular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/ee55facb-7401-5f9c-9aa4-280c0f98b628
-- title:
--   Dimension-shift kernel of the trivial module is the augmentation ideal
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe). Write $A =$ `Rep.trivial k G k` for the trivial $k$-linear representation of $G$ on $k$, let $A$.`indBot` be the representation induced from the restriction of $A$ to the trivial subgroup $\bot \le G$, and let $A$.`dimShiftDownObj` be the subrepresentation of $A$.`indBot` cut out by the kernel of the linear map underlying the morphism `indBotπ` $A$ (the morphism characterised by [`Rep.indBotPi_indBotMk`](thm.html#Rep.indBotPi_indBotMk), which sends the generator $A$.`indBotMk` $g\,a$ to $A$.$\rho(g^{-1})a$). Let [`Rep.leftRegularFinsupp k G`](def/Compat_Mathlib430.html#L103) be $G \to_{0} k$ with $G$ acting by permuting the basis along $h \mapsto g\cdot h$. The assertion is that there exists a morphism of representations $j \colon A.\mathrm{dimShiftDownObj} \to k[G]$ such that: the underlying map of $j$ is injective; the augmentation $f \mapsto \sum_{g} f(g)$, expressed as `Finsupp.linearCombination k (fun _ => 1)`, vanishes on every value of $j$; conversely every $f \colon G \to_{0} k$ with $\sum_g f(g) = 0$ lies in the range of the linear map underlying $j$; and for each $g \in G$ there is an element $d$ of $A.\mathrm{dimShiftDownObj}$ with $j(d) = e_g - e_1$. The last clause is an instance of the third, recorded separately for use.
--
--   This identifies the kernel of the dimension-shifting augmentation for the trivial module with the augmentation ideal of the group ring $k[G]$, equivariantly for the left regular action, thereby providing explicit generators $e_g - e_1$ of that kernel. It is used in the construction underlying [`Rep.exists_shortExact_map_two_eq_zero`](thm.html#Rep.exists_shortExact_map_two_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_hom_dimShiftDownObj_trivial_leftRegular.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.exists_hom_dimShiftDownObj_trivial_leftRegular {k G : Type u} [CommRing k] [Group G] :
    ∃ j : (Rep.trivial k G k).dimShiftDownObj ⟶ Rep.leftRegularFinsupp k G,
      Function.Injective j.hom ∧
      (∀ x, Finsupp.linearCombination k (fun _ : G => (1 : k)) (j.hom x) = 0) ∧
      (∀ f : G →₀ k, Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0 → f ∈ LinearMap.range j.hom.toLinearMap) ∧
      (∀ g : G, ∃ d : (Rep.trivial k G k).dimShiftDownObj, j.hom d = Finsupp.single g 1 - Finsupp.single 1 1) := by sorry
