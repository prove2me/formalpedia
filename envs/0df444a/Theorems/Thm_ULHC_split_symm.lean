-- Prove2me | Theorems.Thm_ULHC_split_symm
-- name    : ULHC.split_symm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:54:03.329598+00:00
-- url     : https://prove2.me/theorems/1cb2f886-4db9-4024-ada2-8c9033d59acb
-- title:
--   ULHC: split symm
-- statement:
--   The ULHC construction uses the split symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L82-L114
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L82-L114

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.split_symm (hG : Deg2 V G) {u v : Pt} {s tf : Side} (hu : IsCell V u) (hv : IsCell V v)
    (lu1 : lat1 u s ∈ G) (lu2 : lat2 u s ∈ G) (bu : back u s ∉ G) (fu : front u s ∉ G)
    (lv1 : lat1 v tf ∈ G) (lv2 : lat2 v tf ∈ G) (bv : back v tf ∉ G) (fv : front v tf ∉ G)
    (hsu : Conn G (back1 u s) (back2 u s)) (hsv : Conn G (back1 v tf) (back2 v tf))
    (hdisj : ∀ e, e ∈ cellE u → e ∉ cellE v) :
    Conn (flip G u) (back1 v tf) (back2 v tf) ↔ Conn (flip G v) (back1 u s) (back2 u s) := by sorry
