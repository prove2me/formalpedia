-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_hasSum_coprime_pairs__627280c9885d
-- name    : P2M_FixedOrderFactor_hasSum_coprime_pairs__627280c9885d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:01.875361+00:00
-- url     : https://prove2.me/theorems/0bb06d6d-5410-5ea1-9533-74d130e379c1
-- title:
--   P2 M Fixed Order Factor has Sum coprime pairs  627280c9885d: P2 M Fixed Order Factor has Sum coprime pairs  627280c9885d
-- statement:
--   The P2 M Fixed Order Factor has Sum coprime pairs  627280c9885d construction uses the P2 M Fixed Order Factor has Sum coprime pairs  627280c9885d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L70-L145
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L70-L145

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_hasSum_coprime_pairs__627280c9885d (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasSum (pairTerm N r) (correctionFactor N r) := by sorry

alias «FixedOrderFactor».«hasSum_coprime_pairs'» := P2M_FixedOrderFactor_hasSum_coprime_pairs__627280c9885d
