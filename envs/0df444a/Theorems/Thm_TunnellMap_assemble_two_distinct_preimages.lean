-- Prove2me | Theorems.Thm_TunnellMap_assemble_two_distinct_preimages
-- name    : TunnellMap.assemble_two_distinct_preimages
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:51.225912+00:00
-- url     : https://prove2.me/theorems/a88dac03-92f9-5e49-ad63-c4f452438870
-- title:
--   Tunnell Map: assemble two distinct preimages
-- statement:
--   The Tunnell Map construction uses the assemble two distinct preimages property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L46-L51
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L46-L51

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}

theorem TunnellMap.assemble_two_distinct_preimages (even : E ≃ A) (odd : O ≃ A)
    (a : A) :
    assemble even odd (Sum.inl (even.symm a)) = a ∧
      assemble even odd (Sum.inr (odd.symm a)) = a ∧
      Sum.inl (even.symm a) ≠ Sum.inr (odd.symm a) := by sorry
