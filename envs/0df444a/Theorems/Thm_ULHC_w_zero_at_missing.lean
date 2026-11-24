-- Prove2me | Theorems.Thm_ULHC_w_zero_at_missing
-- name    : ULHC.w_zero_at_missing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:51:12.550281+00:00
-- url     : https://prove2.me/theorems/29ec2c8a-aafc-4a10-a44e-904d4c3b3f61
-- title:
--   ULHC: w zero at missing
-- statement:
--   The ULHC construction uses the w zero at missing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L254-L259
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L254-L259

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE
omit hb

theorem ULHC.w_zero_at_missing {a : Pt} (ha : a ∉ V) {e : Edge} (h : e.p = a ∨ e.q = a) : w e = 0 := by sorry
