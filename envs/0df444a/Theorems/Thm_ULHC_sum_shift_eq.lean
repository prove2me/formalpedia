-- Prove2me | Theorems.Thm_ULHC_sum_shift_eq
-- name    : ULHC.sum_shift_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:07.942427+00:00
-- url     : https://prove2.me/theorems/cd50b909-ed1c-41c6-a2c0-29c1662add08
-- title:
--   ULHC: sum shift eq
-- statement:
--   The ULHC construction uses the sum shift eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L256-L270
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L256-L270

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.sum_shift_eq {F : Finset Edge} {K : Finset Pt} (hK : Closed F K)
    (s : Pt → Pt) (tf : Pt → Pt) (hst : ∀ x, tf (s x) = x) (hts : ∀ x, s (tf x) = x)
    (g g' : Pt → Edge) (hg : ∀ x, g' (s x) = g x)
    (hadj : ∀ x, g x ∈ F → Adj F x (s x)) (hadj' : ∀ x, g' x ∈ F → Adj F x (tf x)) :
    ((K.filter (fun x => g x ∈ F)).card) = ((K.filter (fun x => g' x ∈ F)).card) := by sorry
