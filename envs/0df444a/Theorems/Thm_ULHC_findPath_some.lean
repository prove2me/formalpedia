-- Prove2me | Theorems.Thm_ULHC_findPath_some
-- name    : ULHC.findPath_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:19:31.016347+00:00
-- url     : https://prove2.me/theorems/cff0efc5-a675-4469-b9c3-a7b8b0c1afbd
-- title:
--   ULHC: find Path some
-- statement:
--   The ULHC construction uses the find Path some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L322-L340
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L322-L340

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.findPath_some (hGV : Inside V G) {σ : StripSpec} {L : List StripSpec}
    (h : findPath V G = some (σ, L)) :
    CRPathCA V G σ L ∧ ∀ σ' L', CRPathCA V G σ' L' → wt σ L ≤ wt σ' L' := by sorry
