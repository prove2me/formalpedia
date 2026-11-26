-- Prove2me | Theorems.Thm_P2M_BKAR_Forest_exists_followOrder__eq_some_support_of_mem_edgeSetOrders_94b5d7b04ff1
-- name    : P2M_BKAR_Forest_exists_followOrder__eq_some_support_of_mem_edgeSetOrders_94b5d7b04ff1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:07:02.315602+00:00
-- url     : https://prove2.me/theorems/9c9a16df-b731-5b17-b84c-6640355a3e11
-- title:
--   P2 M BKAR Forest exists follow Order  eq some support of mem edge Set Orders 94b5d7b04ff1: P2 M BKAR Forest exists follow Order  eq some support of mem edge Set Orders 94b5d7b04ff1
-- statement:
--   Every canonical order of a forest index follows to some `Forest` representative whose
--   support is exactly that index, independently of the extension choices.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L164-L186
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L164-L186

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem P2M_BKAR_Forest_exists_followOrder__eq_some_support_of_mem_edgeSetOrders_94b5d7b04ff1
    (choices : ActiveExtensionChoice V)
    {I : ForestIndex V} {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges) :
    ∃ G : Forest V,
      followOrder? choices (Forest.empty V) order = some G ∧
        G.support = I := by sorry

alias «BKAR».«Forest».«exists_followOrder?_eq_some_support_of_mem_edgeSetOrders» := P2M_BKAR_Forest_exists_followOrder__eq_some_support_of_mem_edgeSetOrders_94b5d7b04ff1
