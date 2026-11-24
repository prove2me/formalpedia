-- Prove2me | Theorems.Thm_ULHC_theoremA
-- name    : ULHC.theoremA
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:49:27.419417+00:00
-- url     : https://prove2.me/theorems/467ac604-77e0-4b1c-a28e-897119aecb70
-- title:
--   ULHC: theorem A
-- statement:
--   **Theorem A** (thesis Lemma 6.7 with Lemma 6.6). In a solid grid graph with a
--   Hamiltonian cycle `H`, every 2-factor `F` with at least two components has a valid
--   alternating strip sequence, and flipping it leaves one component fewer.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L261-L283
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L261-L283

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.theoremA {V : Finset Pt} {H : Finset Edge} (hs : Solid V) (hH : Deg2 V H)
    (hHam : ncomp V H = 1) (F : Finset Edge) (hF : Deg2 V F) (h2 : 2 ≤ ncomp V F) :
    ∃ L : List StripSpec, ValidSeq V F L ∧ ncomp V (applySeq F L) + 1 = ncomp V F := by sorry
