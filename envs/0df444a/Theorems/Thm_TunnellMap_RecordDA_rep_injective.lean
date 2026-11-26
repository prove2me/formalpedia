-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_rep_injective
-- name    : TunnellMap.RecordDA.rep_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:27:58.079043+00:00
-- url     : https://prove2.me/theorems/66c05090-bbd8-5711-a0cc-f529d77c5bee
-- title:
--   Record DA: rep injective
-- statement:
--   The Record DA construction uses the rep injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L196-L199
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L196-L199

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}

theorem TunnellMap.RecordDA.rep_injective :
    Function.Injective (canonicalBResidualRepresentative (n := n)) := by sorry
