-- Prove2me | Theorems.Thm_ULHC_pot_around_missing
-- name    : ULHC.pot_around_missing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:42:31.744083+00:00
-- url     : https://prove2.me/theorems/64a66237-e36f-44cf-a479-9fdabca38832
-- title:
--   ULHC: pot around missing
-- statement:
--   The ULHC construction uses the pot around missing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L261-L266
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L261-L266

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE

theorem ULHC.pot_around_missing {a c : Pt} (ha : a ∉ V) (hc : Around a c) : pot E w c = pot E w a := by sorry
