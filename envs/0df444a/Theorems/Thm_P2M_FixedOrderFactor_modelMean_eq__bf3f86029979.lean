-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_modelMean_eq__bf3f86029979
-- name    : P2M_FixedOrderFactor_modelMean_eq__bf3f86029979
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:15.036319+00:00
-- url     : https://prove2.me/theorems/90ab56be-d018-45e3-9d5d-4a7e3c18af4e
-- title:
--   P2 M Fixed Order Factor model Mean eq  bf3f86029979: P2 M Fixed Order Factor model Mean eq  bf3f86029979
-- statement:
--   The P2 M Fixed Order Factor model Mean eq  bf3f86029979 construction uses the P2 M Fixed Order Factor model Mean eq  bf3f86029979 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L27-L37
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L27-L37

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_modelMean_eq__bf3f86029979 (r : ℕ) (S : Finset Nat.Primes) :
    modelMean r S = ∏ q ∈ S, muAvg r (1 / (q : ℝ)) := by sorry

alias «FixedOrderFactor».«modelMean_eq'» := P2M_FixedOrderFactor_modelMean_eq__bf3f86029979
