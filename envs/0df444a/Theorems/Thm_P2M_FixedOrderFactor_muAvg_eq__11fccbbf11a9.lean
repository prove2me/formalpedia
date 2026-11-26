-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_muAvg_eq__11fccbbf11a9
-- name    : P2M_FixedOrderFactor_muAvg_eq__11fccbbf11a9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:13.740978+00:00
-- url     : https://prove2.me/theorems/d7ed74cf-7a0d-444d-9ab8-faa13820c2fe
-- title:
--   P2 M Fixed Order Factor mu Avg eq  11fccbbf11a9: P2 M Fixed Order Factor mu Avg eq  11fccbbf11a9
-- statement:
--   The P2 M Fixed Order Factor mu Avg eq  11fccbbf11a9 construction uses the P2 M Fixed Order Factor mu Avg eq  11fccbbf11a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L76-L116
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L76-L116

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_muAvg_eq__11fccbbf11a9 {r : ℕ} (hr : 0 < r) {x : ℝ} (hx : |x| < 1) :
    muAvg r x = (1 + x ^ r) / ((1 - x ^ 2) * (1 - x ^ r)) := by sorry

alias «FixedOrderFactor».«muAvg_eq'» := P2M_FixedOrderFactor_muAvg_eq__11fccbbf11a9
