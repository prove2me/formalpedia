-- Prove2me | Theorems.Thm_ULHC_one_strip_P
-- name    : ULHC.one_strip_P
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:45:50.426847+00:00
-- url     : https://prove2.me/theorems/604a58a0-2b3a-495c-99d8-1ac68ecc4f57
-- title:
--   ULHC: one strip P
-- statement:
--   The ULHC construction uses the one strip P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L69-L107
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L69-L107

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam

theorem ULHC.one_strip_P {F : Finset Edge} (hF : Deg2 V F) (hT : NoTypeIII V F) {P : Finset Pt}
    (hB : Border V F P) {x y : Pt} (hx : x ∈ V) (hy : y ∈ V) (hxP : x ∈ P) (hyP : y ∉ P) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      ∃ si, Cut P (sideEdge σ.c si) := by sorry
