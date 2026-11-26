-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_quartic_constants__3ebcdb63d740
-- name    : P2M_FixedOrderFactor_quartic_constants__3ebcdb63d740
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:08.60446+00:00
-- url     : https://prove2.me/theorems/f2b33869-4a5c-50d4-b7ee-cf46db2fba8d
-- title:
--   P2 M Fixed Order Factor quartic constants  3ebcdb63d740: P2 M Fixed Order Factor quartic constants  3ebcdb63d740
-- statement:
--   The P2 M Fixed Order Factor quartic constants  3ebcdb63d740 construction uses the P2 M Fixed Order Factor quartic constants  3ebcdb63d740 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L99-L107
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L99-L107

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_quartic_constants__3ebcdb63d740 :
    (4 / 5) * zetaN {two} 2 = π ^ 2 / 10 ∧
    (4 / 5) * zetaN {two} 2 * correctionFactor {two} 4 = 7 * π ^ 2 / 68 ∧
    zetaN ∅ 2 * correctionFactor ∅ 4 = 7 * π ^ 2 / 36 ∧
    (7 : ℝ) / 136 = 1 / 20 * (35 / 34) ∧ (7 : ℝ) / 136 = 7 / 72 * (9 / 17) := by sorry

alias «FixedOrderFactor».«quartic_constants'» := P2M_FixedOrderFactor_quartic_constants__3ebcdb63d740
