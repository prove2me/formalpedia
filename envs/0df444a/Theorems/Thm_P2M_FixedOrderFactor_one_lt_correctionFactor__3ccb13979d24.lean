-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_one_lt_correctionFactor__3ccb13979d24
-- name    : P2M_FixedOrderFactor_one_lt_correctionFactor__3ccb13979d24
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:53.059794+00:00
-- url     : https://prove2.me/theorems/21a9d1e6-b22d-4dd2-a221-dcd18be3f3a0
-- title:
--   P2 M Fixed Order Factor one lt correction Factor  3ccb13979d24: P2 M Fixed Order Factor one lt correction Factor  3ccb13979d24
-- statement:
--   The P2 M Fixed Order Factor one lt correction Factor  3ccb13979d24 construction uses the P2 M Fixed Order Factor one lt correction Factor  3ccb13979d24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L39-L46
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L39-L46

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_one_lt_correctionFactor__3ccb13979d24 (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    1 < correctionFactor N r := by sorry

alias «FixedOrderFactor».«one_lt_correctionFactor'» := P2M_FixedOrderFactor_one_lt_correctionFactor__3ccb13979d24
