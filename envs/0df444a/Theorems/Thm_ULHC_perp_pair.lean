-- Prove2me | Theorems.Thm_ULHC_perp_pair
-- name    : ULHC.perp_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:56:37.198011+00:00
-- url     : https://prove2.me/theorems/4424236b-e5eb-4cc7-870f-acf7d4891b79
-- title:
--   ULHC: perp pair
-- statement:
--   The ULHC construction uses the perp pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L120-L126
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L120-L126

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.perp_pair (d : Pt) {s tf : Side} (ht : tf = latA s ∨ tf = latB s) :
    (back1 d tf = back1 d s ∧ front1 d tf = back2 d s) ∨
      (back1 d tf = back2 d s ∧ front1 d tf = back1 d s) ∨
      (back1 d tf = front1 d s ∧ front1 d tf = front2 d s) ∨
      (back1 d tf = front2 d s ∧ front1 d tf = front1 d s) := by sorry
