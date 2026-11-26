-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
-- name    : TunnellMap.GloballyRanked.insertEquiv_at_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:43.31626+00:00
-- url     : https://prove2.me/theorems/fde13e8d-6a99-5519-87aa-af37a969f05e
-- title:
--   Globally Ranked: insert Equiv at left
-- statement:
--   The Globally Ranked construction uses the insert Equiv at left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRankedExistence.lean#L38-L41
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRankedExistence.lean#L38-L41

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_GloballyRankedExistence
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}

theorem TunnellMap.GloballyRanked.insertEquiv_at_left [DecidableEq S] [DecidableEq T]
    (s₀ : S) (t₀ : T) (M' : {s // s ≠ s₀} ≃ {t // t ≠ t₀}) :
    insertEquiv s₀ t₀ M' s₀ = t₀ := by sorry
