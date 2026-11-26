-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_hasProd_correctionFactor__ac45d6c11465
-- name    : P2M_FixedOrderFactor_hasProd_correctionFactor__ac45d6c11465
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:01.377626+00:00
-- url     : https://prove2.me/theorems/29bed0fe-8008-42a1-8003-0bf03954b0d2
-- title:
--   P2 M Fixed Order Factor has Prod correction Factor  ac45d6c11465: P2 M Fixed Order Factor has Prod correction Factor  ac45d6c11465
-- statement:
--   The P2 M Fixed Order Factor has Prod correction Factor  ac45d6c11465 construction uses the P2 M Fixed Order Factor has Prod correction Factor  ac45d6c11465 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L123-L138
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L123-L138

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor

theorem P2M_FixedOrderFactor_hasProd_correctionFactor__ac45d6c11465 (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} =>
        (1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r))
      (correctionFactor N r) := by sorry

alias «FixedOrderFactor».«hasProd_correctionFactor'» := P2M_FixedOrderFactor_hasProd_correctionFactor__ac45d6c11465
