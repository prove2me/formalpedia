-- Prove2me | Theorems.Thm_ULHC_pot_missing_chain
-- name    : ULHC.pot_missing_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:51:12.929595+00:00
-- url     : https://prove2.me/theorems/d3201603-b23f-462f-bbd6-6ab879e3fc8f
-- title:
--   ULHC: pot missing chain
-- statement:
--   The ULHC construction uses the pot missing chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L268-L279
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L268-L279

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE

theorem ULHC.pot_missing_chain {a b : Pt} (h : Relation.ReflTransGen (MissAdj V) a b) :
    pot E w a = pot E w b := by sorry
