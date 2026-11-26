-- Prove2me | Theorems.Thm_TunnellMap_sourceRosterExec_pairwise
-- name    : TunnellMap.sourceRosterExec_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:18:46.894148+00:00
-- url     : https://prove2.me/theorems/698382fd-00d5-49db-a538-fe09f07b94dd
-- title:
--   Tunnell Map: source Roster Exec pairwise
-- statement:
--   The Tunnell Map construction uses the source Roster Exec pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L183-L187
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L183-L187

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.sourceRosterExec_pairwise {n : ℤ} :
    (sourceRosterExec n).Pairwise fun a b => bResidualLexKey a ≤ bResidualLexKey b := by sorry
