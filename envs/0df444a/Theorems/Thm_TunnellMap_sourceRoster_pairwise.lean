-- Prove2me | Theorems.Thm_TunnellMap_sourceRoster_pairwise
-- name    : TunnellMap.sourceRoster_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:20:46.477203+00:00
-- url     : https://prove2.me/theorems/0333d175-63ad-463a-90f7-2b98c6e13970
-- title:
--   Tunnell Map: source Roster pairwise
-- statement:
--   The Tunnell Map construction uses the source Roster pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L262-L273
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L262-L273

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap
variable {n : ℤ} [Fintype (BOddRep n)]
open RecordDA

theorem TunnellMap.sourceRoster_pairwise :
    (sourceRoster n).Pairwise fun a b => bResidualLexKey a ≤ bResidualLexKey b := by sorry
