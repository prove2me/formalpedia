-- Prove2me | Theorems.Thm_ULHC_one_strip
-- name    : ULHC.one_strip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:42:21.054037+00:00
-- url     : https://prove2.me/theorems/14243b86-3e7b-4bb0-947e-295386608dd3
-- title:
--   ULHC: one strip
-- statement:
--   The ULHC construction uses the one strip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L214-L254
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L214-L254

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam

theorem ULHC.one_strip {F : Finset Edge} (hF : Deg2 V F) (hT : NoTypeIII V F) (h2 : 2 ≤ ncomp V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H := by sorry
