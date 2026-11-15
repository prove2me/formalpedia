-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_ArrayEquality_array_equality_program
-- name    : StableMSR.Recovery.Compiler.ArrayEquality.array_equality_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-15T01:30:02.478127+00:00
-- url     : https://prove2.me/theorems/4aa4afb9-0474-46c8-8737-049c59c97e20
-- title:
--   A fixed charged program deciding integer-array equality
-- statement:
--   One deterministic program with $22$ instructions decides equality of two integer arrays of length $L$, supplied by their ordinary memory addresses. It initializes its own Boolean flag, examines every corresponding cell, and halts after exactly
--
--   $$11L+7$$
--
--   charged interpreter steps. Its output flag is $1$ exactly when the arrays agree at every position, and $0$ exactly when some position differs. The result includes $L=0$, arbitrary integer entries, arbitrary initial scratch registers, and overlapping input arrays. Every integer and real memory cell, all real registers, the input metadata, and oracle/tape counts are preserved. No equality result is provided as input advice. This is the executable comparison primitive used by boundary checks and finite state-table lookup.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; executable comparisons and state-table lookup supporting rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
import Mathlib.Combinatorics.SimpleGraph.Basic
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.ArrayEquality.array_equality_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 22 ∧
      ∀ (N L : ℕ) (d : Point N → Point N → ℝ) (ω : ℕ → ℝ)
        (s : Store) (w : ℕ), s.ptrs 6 = (L : ℤ) →
        ∃ t : Store,
          (t.ptrs 18 = 0 ∨ t.ptrs 18 = 1) ∧
          (t.ptrs 18 = 1 ↔ ∀ i : Fin L,
            s.imem (s.ptrs 3+(i.val : ℤ)) = s.imem (s.ptrs 4+(i.val : ℤ))) ∧
          (t.ptrs 18 = 0 ↔ ∃ i : Fin L,
            s.imem (s.ptrs 3+(i.val : ℤ)) ≠ s.imem (s.ptrs 4+(i.val : ℤ))) ∧
          (∀ j : ℕ, j ≠ 0 → j ≠ 18 → j ≠ 20 →
            j ≠ 21 → j ≠ 22 → j ≠ 23 → t.ptrs j = s.ptrs j) ∧
          t.regs = s.regs ∧ t.mem = s.mem ∧ t.imem = s.imem ∧
          t.queries = s.queries ∧ t.tapePos = s.tapePos ∧ t.output = s.output ∧
          (MinSumFPT.step P d ω)^[11*L+7] (s.state 0 w) =
            t.haltedState 21 (w+(11*L+7)) 0 := by sorry
