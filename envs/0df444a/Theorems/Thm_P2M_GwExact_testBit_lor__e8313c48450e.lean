-- Prove2me | Theorems.Thm_P2M_GwExact_testBit_lor__e8313c48450e
-- name    : P2M_GwExact_testBit_lor__e8313c48450e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:20:26.111775+00:00
-- url     : https://prove2.me/theorems/c6cd7eec-813e-4e93-835a-08487ed14549
-- title:
--   P2 M Gw Exact test Bit lor  e8313c48450e: P2 M Gw Exact test Bit lor  e8313c48450e
-- statement:
--   The P2 M Gw Exact test Bit lor  e8313c48450e construction uses the P2 M Gw Exact test Bit lor  e8313c48450e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L112-L113
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L112-L113

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem P2M_GwExact_testBit_lor__e8313c48450e (a b u : Nat) : (Nat.lor a b).testBit u = (a.testBit u || b.testBit u) := by sorry

alias «GwExact».«testBit_lor'» := P2M_GwExact_testBit_lor__e8313c48450e
