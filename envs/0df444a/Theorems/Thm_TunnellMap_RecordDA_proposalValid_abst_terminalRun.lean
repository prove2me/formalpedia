-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_proposalValid_abst_terminalRun
-- name    : TunnellMap.RecordDA.proposalValid_abst_terminalRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:16:15.601457+00:00
-- url     : https://prove2.me/theorems/a05261ba-992a-4dc6-890b-a41b8a95e566
-- title:
--   Record DA: proposal Valid abst terminal Run
-- statement:
--   The Record DA construction uses the proposal Valid abst terminal Run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L850-L855
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean#L850-L855

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.proposalValid_abst_terminalRun (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) :
    (abst hn hnpos frames (terminalRun frames)).ProposalValid
      (residualOrbitRanking hnpos) := by sorry
