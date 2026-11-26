-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_advance_isNone_iff
-- name    : TunnellMap.RecordDA.advance_isNone_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:28:40.479945+00:00
-- url     : https://prove2.me/theorems/08dd3939-353e-4f32-bda3-e8d6cc89bedc
-- title:
--   Record DA: advance is None iff
-- statement:
--   The Record DA construction uses the advance is None iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L260-L268
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L260-L268

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
omit [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.advance_isNone_iff (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (g : GenState) :
    BlockGen.advance s F g = none ↔ remainingTrace s F g = [] := by sorry
