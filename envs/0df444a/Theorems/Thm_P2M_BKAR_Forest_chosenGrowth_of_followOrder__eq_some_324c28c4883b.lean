-- Prove2me | Theorems.Thm_P2M_BKAR_Forest_chosenGrowth_of_followOrder__eq_some_324c28c4883b
-- name    : P2M_BKAR_Forest_chosenGrowth_of_followOrder__eq_some_324c28c4883b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:07:00.472556+00:00
-- url     : https://prove2.me/theorems/135cdcb0-c291-5904-b11a-7b32ee83fdb6
-- title:
--   P2 M BKAR Forest chosen Growth of follow Order  eq some 324c28c4883b: P2 M BKAR Forest chosen Growth of follow Order  eq some 324c28c4883b
-- statement:
--   The P2 M BKAR Forest chosen Growth of follow Order  eq some 324c28c4883b construction uses the P2 M BKAR Forest chosen Growth of follow Order  eq some 324c28c4883b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L71-L85
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L71-L85

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem P2M_BKAR_Forest_chosenGrowth_of_followOrder__eq_some_324c28c4883b
    (choices : ActiveExtensionChoice V) :
    ∀ {F G : Forest V} {order : List (Edge V)},
      followOrder? choices F order = some G →
      ChosenGrowth choices F order G
  := by sorry

alias «BKAR».«Forest».«chosenGrowth_of_followOrder?_eq_some» := P2M_BKAR_Forest_chosenGrowth_of_followOrder__eq_some_324c28c4883b
