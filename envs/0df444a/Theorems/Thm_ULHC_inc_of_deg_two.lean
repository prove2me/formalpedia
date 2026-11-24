-- Prove2me | Theorems.Thm_ULHC_inc_of_deg_two
-- name    : ULHC.inc_of_deg_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:08.775607+00:00
-- url     : https://prove2.me/theorems/0e08bfc7-0897-4918-86b6-577c9d4883fd
-- title:
--   ULHC: inc of deg two
-- statement:
--   The ULHC construction uses the inc of deg two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L407-L420
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L407-L420

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.inc_of_deg_two {F : Finset Edge} {z : Pt} (hd : deg F z = 2) {e e' f : Edge}
    (he : e ∈ F) (hz : e.p = z ∨ e.q = z) (he' : e' ∈ F) (hz' : e'.p = z ∨ e'.q = z)
    (hne : e ≠ e') (hf : f ∈ F) (hzf : f.p = z ∨ f.q = z) : f = e ∨ f = e' := by sorry
