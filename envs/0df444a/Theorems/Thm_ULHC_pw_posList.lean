-- Prove2me | Theorems.Thm_ULHC_pw_posList
-- name    : ULHC.pw_posList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:37:11.511151+00:00
-- url     : https://prove2.me/theorems/0a1ec82b-182e-46c1-ae93-f4b9e9d58d2a
-- title:
--   ULHC: pw pos List
-- statement:
--   The ULHC construction uses the pw pos List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L118-L123
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L118-L123

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.pw_posList : ∀ (L : List StripSpec) (k : ℕ),
    MP.pw gw (posList k L) = (L.map StripSpec.n).sum
  := by sorry
