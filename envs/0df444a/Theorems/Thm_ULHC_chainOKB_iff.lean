-- Prove2me | Theorems.Thm_ULHC_chainOKB_iff
-- name    : ULHC.chainOKB_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:36:49.188091+00:00
-- url     : https://prove2.me/theorems/958fc363-4059-458f-92ac-ab8533e6ccff
-- title:
--   ULHC: chain OKB iff
-- statement:
--   The ULHC construction uses the chain OKB iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L47-L48
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L47-L48

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.chainOKB_iff {b c : StripSpec} : chainOKB b c = true ↔ ChainOK b c := by sorry
