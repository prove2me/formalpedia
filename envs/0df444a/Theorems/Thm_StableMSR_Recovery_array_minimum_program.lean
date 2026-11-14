-- Prove2me | Theorems.Thm_StableMSR_Recovery_array_minimum_program
-- name    : StableMSR.Recovery.array_minimum_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T02:23:51.042257+00:00
-- url     : https://prove2.me/theorems/0aea05ce-c128-4474-ad63-c10e32c5a519
-- title:
--   A fixed deterministic array-minimum program with exact linear execution cost
-- statement:
--   There is one admissible deterministic program that scans any nonempty array of q+1 real numbers stored at consecutive addresses. The initial pointer registers specify the first and last addresses. Starting at program counter zero in a nonhalted state, the actual interpreter halts after exactly 8q+6 instructions, returns the minimum as its real output, and places a minimizing address in pointer register 2. Charged work increases by exactly the same amount. Both memory arrays, the distance-query count, and the random-tape position are preserved. This is a concrete reusable minimum-selection block for the stable clustering recovery program; it does not itself enumerate candidates or solve the whole clustering instance.
-- source:
--   Implementation lemma for the Prove2Me mission Exact Sum-of-Radii Clustering under Any Constant Stability; finite minimum selection in the charged MinSumFPT real-RAM interpreter.

import Definitions.Def_StableMSR_Recovery_Execution
open StableMSR.Recovery

theorem StableMSR.Recovery.array_minimum_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
      ∀ (n : ℕ) (d : Point n → Point n → ℝ) (s : MinSumFPT.State) (q : ℕ),
        s.cfg.pc = 0 → s.halted = false → s.cfg.ptrs 1 = s.cfg.ptrs 0 + (q : ℤ) →
        ∀ ω : ℕ → ℝ,
        let result := (MinSumFPT.step P d ω)^[8*q+6] s
        result.halted = true ∧ result.work = s.work+8*q+6 ∧
        (∃ j ≤ q, result.cfg.ptrs 2 = s.cfg.ptrs 0 + (j : ℤ) ∧
          result.output = s.cfg.mem (s.cfg.ptrs 0 + j) ∧
          ∀ i ≤ q, result.output ≤ s.cfg.mem (s.cfg.ptrs 0 + (i : ℤ))) ∧
        result.cfg.mem = s.cfg.mem ∧ result.imem = s.imem ∧
        result.queries = s.queries ∧ result.tapePos = s.tapePos := by sorry
