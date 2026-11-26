-- Prove2me | Theorems.Thm_P2M_BKAR_Forest_exists_followOrder__eq_some_of_acyclic_union_cd131d32a109
-- name    : P2M_BKAR_Forest_exists_followOrder__eq_some_of_acyclic_union_cd131d32a109
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:18:47.560855+00:00
-- url     : https://prove2.me/theorems/8452ffca-2e75-4768-b23c-07a8d5b4fd9e
-- title:
--   P2 M BKAR Forest exists follow Order  eq some of acyclic union cd131d32a109: P2 M BKAR Forest exists follow Order  eq some of acyclic union cd131d32a109
-- statement:
--   Canonical orders of an acyclic target support can be followed through any
--   choice of active extensions. The invariant says that the current
--   `Forest` representative carries the already-consumed prefix, while `order` is the remaining
--   suffix and `S` is the final edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L93-L158
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L93-L158

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem P2M_BKAR_Forest_exists_followOrder__eq_some_of_acyclic_union_cd131d32a109
    (choices : ActiveExtensionChoice V) :
    ∀ {F : Forest V} {S : Finset (Edge V)} (order : List (Edge V)),
      IsAcyclicEdgeSet S →
      order.toFinset ∪ F.edges = S →
      order.Nodup →
      Disjoint order.toFinset F.edges →
      ∃ G : Forest V, followOrder? choices F order = some G ∧
        G.edges = S
  := by sorry

alias «BKAR».«Forest».«exists_followOrder?_eq_some_of_acyclic_union» := P2M_BKAR_Forest_exists_followOrder__eq_some_of_acyclic_union_cd131d32a109
