-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_localTerm_I_half__1a94193266fb
-- name    : P2M_FixedOrderFactor_localTerm_I_half__1a94193266fb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:49.678409+00:00
-- url     : https://prove2.me/theorems/e9d319ba-2dcb-5b51-9917-d070bab63074
-- title:
--   P2 M Fixed Order Factor local Term I half  1a94193266fb: P2 M Fixed Order Factor local Term I half  1a94193266fb
-- statement:
--   The P2 M Fixed Order Factor local Term I half  1a94193266fb construction uses the P2 M Fixed Order Factor local Term I half  1a94193266fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L88-L90
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L88-L90

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_localTerm_I_half__1a94193266fb : localTerm Complex.I (1 / 2) = 4 / 5 ∧
    localTerm (-Complex.I) (1 / 2) = 4 / 5 := by sorry

alias «FixedOrderFactor».«localTerm_I_half'» := P2M_FixedOrderFactor_localTerm_I_half__1a94193266fb
