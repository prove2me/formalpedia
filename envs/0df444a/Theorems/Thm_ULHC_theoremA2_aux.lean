-- Prove2me | Theorems.Thm_ULHC_theoremA2_aux
-- name    : ULHC.theoremA2_aux
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:46:07.720877+00:00
-- url     : https://prove2.me/theorems/8cf59299-6f4e-43ea-90dc-8c967c466187
-- title:
--   ULHC: theorem A2 aux
-- statement:
--   The ULHC construction uses the theorem A2 aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L125-L194
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L125-L194

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam

theorem ULHC.theoremA2_aux : ∀ m (F : Finset Edge) (a : Option Pt), mu V F H = m → Deg2 V F →
    2 ≤ ncomp V F → AnchorOK V F a → ∃ L : List StripSpec, ValidSeqA V a F L := by sorry
