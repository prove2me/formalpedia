-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_BitmapStats_bitmap_statistics_program
-- name    : StableMSR.Recovery.Compiler.BitmapStats.bitmap_statistics_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T20:59:17.247677+00:00
-- url     : https://prove2.me/theorems/ff3d0641-5176-4ec2-b87f-767332b079a6
-- title:
--   A fixed charged program for bitmap cardinality and least vertex
-- statement:
--   There is one deterministic program with $19$ instructions that scans an ordinary zero–one bitmap of a subset $C\subseteq\{0,\ldots,n-1\}$. It initializes its own counters and halts in exactly
--
--   $$9n+8$$
--
--   charged interpreter steps, including every branch, loop test, and the final halt. Register $18$ contains $|C|$. Register $19$ contains the least vertex of $C$ when $C$ is nonempty, and the sentinel $n$ exactly when $C$ is empty. The reported index always lies between $0$ and $n$.
--
--   The theorem covers $n=0$, arbitrary initial counters, arbitrary bitmap addresses, arbitrary distance oracles and tapes, and arbitrary initial work counters. Both integer and real memory, all real registers, the input registers, and oracle/tape counts are preserved. Only the fixed scratch and output pointer registers may change. No cardinality or minimum is supplied as input advice.
--
--   This provides the executable cardinality and representative-index primitive needed to organize component states in decomposition search. It does not itself implement subset ranking, table lookup, or the complete clustering recovery program.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; concrete state-size and representative-index primitive for rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.BitmapStats.bitmap_statistics_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 19 ∧
      ∀ (N n : ℕ) (d : Point N → Point N → ℝ) (ω : ℕ → ℝ)
        (s : Store) (C : Finset (Fin n)) (w : ℕ),
        s.ptrs 6 = (n : ℤ) → Bitmap s.imem (s.ptrs 3) C →
        ∃ t : Store,
          t.ptrs 18 = (C.card : ℤ) ∧
          (t.ptrs 19 = (n : ℤ) ↔ C = ∅) ∧
          (C.Nonempty → ∃ v ∈ C, t.ptrs 19 = (v.val : ℤ) ∧
            ∀ u ∈ C, v.val ≤ u.val) ∧
          (0 ≤ t.ptrs 19 ∧ t.ptrs 19 ≤ (n : ℤ)) ∧
          (∀ j : ℕ, j ≠ 0 → j ≠ 18 → j ≠ 19 → j ≠ 20 →
            j ≠ 21 → j ≠ 22 → t.ptrs j = s.ptrs j) ∧
          t.regs = s.regs ∧ t.mem = s.mem ∧ t.imem = s.imem ∧
          t.queries = s.queries ∧ t.tapePos = s.tapePos ∧ t.output = s.output ∧
          (MinSumFPT.step P d ω)^[9*n+8] (s.state 0 w) =
            t.haltedState 18 (w+(9*n+8)) 0 := by sorry
