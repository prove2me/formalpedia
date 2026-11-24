-- Prove2me | Theorems.Thm_ULHC_path_to_crpath
-- name    : ULHC.path_to_crpath
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:29:18.602402+00:00
-- url     : https://prove2.me/theorems/56e83bfd-b4c5-4551-83df-1ff9dd910e67
-- title:
--   ULHC: path to crpath
-- statement:
--   The ULHC construction uses the path to crpath property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L282-L299
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L282-L299

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.path_to_crpath (hGV : Inside V G) {p : List Node}
    (hp : MP.IsPath (gsrc V G) gmid gtgt (gedge V G) p) (hN : ∀ x ∈ p, x ∈ candN V G) :
    ∃ σ L, p = posList 1 (σ :: L) ∧ CRPathCA V G σ L ∧ MP.pw gw p = wt σ L := by sorry
