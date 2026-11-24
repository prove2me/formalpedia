-- Prove2me | Theorems.Thm_ULHC_nOn_eq
-- name    : ULHC.nOn_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:19.995832+00:00
-- url     : https://prove2.me/theorems/0b4577f1-aab2-4e28-a6b3-cacdcd22cbcc
-- title:
--   ULHC: n On eq
-- statement:
--   The ULHC construction uses the n On eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L719-L728
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L719-L728

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.nOn_eq (c : Pt) (s : Side) (n : ℕ) (e : Edge) (J : Finset ℕ)
    (hJ : ∀ j, j < n → (e ∈ cellE (cellJ c s j) ↔ j ∈ J)) (hJn : ∀ j ∈ J, j < n) :
    nOn c s n e = J.card := by sorry
