-- Prove2me | Theorems.Thm_ULHC_crpath_to_path
-- name    : ULHC.crpath_to_path
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:29:17.605818+00:00
-- url     : https://prove2.me/theorems/14743692-344d-4377-add3-bcfda41bf348
-- title:
--   ULHC: crpath to path
-- statement:
--   The ULHC construction uses the crpath to path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L223-L245
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L223-L245

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.crpath_to_path (hGV : Inside V G) {σ : StripSpec} {L : List StripSpec}
    (h : CRPathCA V G σ L) :
    MP.IsPath (gsrc V G) gmid gtgt (gedge V G) (posList 1 (σ :: L)) ∧
      (∀ x ∈ posList 1 (σ :: L), x ∈ candN V G) ∧ MP.pw gw (posList 1 (σ :: L)) = wt σ L := by sorry
