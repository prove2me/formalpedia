-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
-- name    : TunnellMap.GloballyRanked.insertEquiv_symm_at_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:55.609511+00:00
-- url     : https://prove2.me/theorems/21729126-2651-4534-a609-aa7f47cdd5a3
-- title:
--   Globally Ranked: insert Equiv symm at right
-- statement:
--   The Globally Ranked construction uses the insert Equiv symm at right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRankedExistence.lean#L43-L46
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRankedExistence.lean#L43-L46

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_GloballyRankedExistence
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}

theorem TunnellMap.GloballyRanked.insertEquiv_symm_at_right [DecidableEq S] [DecidableEq T]
    (s₀ : S) (t₀ : T) (M' : {s // s ≠ s₀} ≃ {t // t ≠ t₀}) :
    (insertEquiv s₀ t₀ M').symm t₀ = s₀ := by sorry
