-- Prove2me | Theorems.Thm_SizeRamsey_k33MinusEdge_arrows_matching2_c4
-- name    : SizeRamsey.k33MinusEdge_arrows_matching2_c4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:31.259015+00:00
-- url     : https://prove2.me/theorems/c382178d-5d86-4633-bf95-d97c4b664226
-- title:
--   Size Ramsey: k33 Minus Edge arrows matching2 c4
-- statement:
--   The Size Ramsey construction uses the k33 Minus Edge arrows matching2 c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L167-L185
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L167-L185

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.k33MinusEdge_arrows_matching2_c4 :
    ∀ R : SimpleGraph (Fin 6), R ≤ k33MinusEdge →
      HasMatching2 R ∨ HasC4 (k33MinusEdge \ R) := by sorry
