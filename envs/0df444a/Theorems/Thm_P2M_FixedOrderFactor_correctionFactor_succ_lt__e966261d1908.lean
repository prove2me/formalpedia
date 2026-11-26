-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_succ_lt__e966261d1908
-- name    : P2M_FixedOrderFactor_correctionFactor_succ_lt__e966261d1908
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:15.094564+00:00
-- url     : https://prove2.me/theorems/f126a12e-f9ca-4d96-b543-55b832272ac5
-- title:
--   P2 M Fixed Order Factor correction Factor succ lt  e966261d1908: P2 M Fixed Order Factor correction Factor succ lt  e966261d1908
-- statement:
--   The P2 M Fixed Order Factor correction Factor succ lt  e966261d1908 construction uses the P2 M Fixed Order Factor correction Factor succ lt  e966261d1908 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L51-L82
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L51-L82

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_correctionFactor_succ_lt__e966261d1908 (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N (r + 1) < correctionFactor N r := by sorry

alias «FixedOrderFactor».«correctionFactor_succ_lt'» := P2M_FixedOrderFactor_correctionFactor_succ_lt__e966261d1908
