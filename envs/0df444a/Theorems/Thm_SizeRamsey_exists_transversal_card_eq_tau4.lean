-- Prove2me | Theorems.Thm_SizeRamsey_exists_transversal_card_eq_tau4
-- name    : SizeRamsey.exists_transversal_card_eq_tau4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:06.812828+00:00
-- url     : https://prove2.me/theorems/def23abb-75cf-4609-96b1-39f3fe4e5de8
-- title:
--   Size Ramsey: exists transversal card eq tau4
-- statement:
--   The Size Ramsey construction uses the exists transversal card eq tau4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L44-L51
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L44-L51

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.exists_transversal_card_eq_tau4
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ S : Finset V,
      c4Transversal G S ∧ S.card = tau4 G := by sorry
