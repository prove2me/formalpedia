-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_hasProd_muAvg__1e4c6588144b
-- name    : P2M_FixedOrderFactor_hasProd_muAvg__1e4c6588144b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:14.670498+00:00
-- url     : https://prove2.me/theorems/ce1c459d-247c-5891-bf91-7e8917011fb6
-- title:
--   P2 M Fixed Order Factor has Prod mu Avg  1e4c6588144b: P2 M Fixed Order Factor has Prod mu Avg  1e4c6588144b
-- statement:
--   The P2 M Fixed Order Factor has Prod mu Avg  1e4c6588144b construction uses the P2 M Fixed Order Factor has Prod mu Avg  1e4c6588144b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L42-L53
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L42-L53

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_hasProd_muAvg__1e4c6588144b (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => muAvg r (1 / (q : ℝ)))
      (zetaN N 2 * correctionFactor N r) := by sorry

alias «FixedOrderFactor».«hasProd_muAvg'» := P2M_FixedOrderFactor_hasProd_muAvg__1e4c6588144b
