-- Prove2me | Theorems.Thm_P2M_BKAR_Forest_followOrder__grownForestForSupportOrder_bd48bf0ce40b
-- name    : P2M_BKAR_Forest_followOrder__grownForestForSupportOrder_bd48bf0ce40b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:10.234779+00:00
-- url     : https://prove2.me/theorems/8e137faa-785d-430c-8105-d084c46e844f
-- title:
--   P2 M BKAR Forest follow Order  grown Forest For Support Order bd48bf0ce40b: P2 M BKAR Forest follow Order  grown Forest For Support Order bd48bf0ce40b
-- statement:
--   The P2 M BKAR Forest follow Order  grown Forest For Support Order bd48bf0ce40b construction uses the P2 M BKAR Forest follow Order  grown Forest For Support Order bd48bf0ce40b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L55-L63
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L55-L63

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem P2M_BKAR_Forest_followOrder__grownForestForSupportOrder_bd48bf0ce40b
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    followOrder? choices (Forest.empty V) order.val =
      some (grownForestForSupportOrder choices I order) := by sorry

alias «BKAR».«Forest».«followOrder?_grownForestForSupportOrder» := P2M_BKAR_Forest_followOrder__grownForestForSupportOrder_bd48bf0ce40b
