-- Prove2me | Theorems.Thm_ULHC_theorem61
-- name    : ULHC.theorem61
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:21:40.748804+00:00
-- url     : https://prove2.me/theorems/cb87c63e-0100-4e91-b557-e637be78f927
-- title:
--   ULHC: theorem61
-- statement:
--   **Theorem 6.1.** In a solid grid graph with a Hamiltonian cycle, every 2-factor is turned
--   into a single cycle by `ncomp − 1` alternating strip sequences, each valid when applied.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L310-L328
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L310-L328

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.theorem61 {V : Finset Pt} {H : Finset Edge} (hs : Solid V) (hH : Deg2 V H)
    (hHam : ncomp V H = 1) :
    ∀ (F : Finset Edge), Deg2 V F → 1 ≤ ncomp V F →
      ∃ Ls : List (List StripSpec), ValidChain V F Ls ∧ Ls.length + 1 = ncomp V F ∧
        ncomp V (applyChain F Ls) = 1 := by sorry
