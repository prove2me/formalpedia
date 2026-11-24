-- Prove2me | Theorems.Thm_ULHC_theoremA2
-- name    : ULHC.theoremA2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:46:02.556885+00:00
-- url     : https://prove2.me/theorems/d4990ed8-cc68-46ad-beec-a06b05480618
-- title:
--   ULHC: theorem A2
-- statement:
--   **Theorem A2** (thesis Lemma 6.7 with Definition 6.6). In a solid grid graph with a
--   Hamiltonian cycle, every 2-factor with at least two components has a valid sequence in which
--   each strip after the first begins on the chain created by the strip before it; flipping it
--   leaves one component fewer.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L200-L203
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L200-L203

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam

theorem ULHC.theoremA2 (F : Finset Edge) (hF : Deg2 V F) (h2 : 2 ≤ ncomp V F) :
    ∃ L : List StripSpec, ValidSeqA V none F L ∧ ncomp V (applySeq F L) + 1 = ncomp V F := by sorry
