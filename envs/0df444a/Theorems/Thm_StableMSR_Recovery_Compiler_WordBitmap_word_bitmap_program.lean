-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_WordBitmap_word_bitmap_program
-- name    : StableMSR.Recovery.Compiler.WordBitmap.word_bitmap_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-15T18:59:13.625881+00:00
-- url     : https://prove2.me/theorems/b24f4cba-a9da-4349-a699-ab1482f08958
-- title:
--   A fixed charged decoder from integer words to subset bitmaps
-- statement:
--   One fixed deterministic program with $33$ instructions converts an ordinary integer word of length $w$ into an $n$-cell characteristic bitmap. Vertex $v\in\{0,\ldots,n-1\}$ is marked exactly when the digit $v+1$ occurs in the word. Zero is padding; negative digits and digits above $n$ are ignored, and repetitions are harmless.
--
--   The program clears its output, reads and checks each digit, and halts in exactly
--
--   $$4n+11w+12$$
--
--   charged interpreter steps, including initialization, all branches and loop tests, and halt. The source word must avoid the writable output bitmap; the output's initial contents and all scratch registers are unrestricted. Every integer cell outside the bitmap, all real registers/memory, input metadata, and oracle/tape counts are preserved. Empty words and $n=0$ are covered. The program is chosen before the dimensions, word, and oracle. This supplies the executable conversion from bounded-subset catalog records to the characteristic keys used by the graph and table primitives.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; executable subset-key generation and table construction supporting rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler

theorem StableMSR.Recovery.Compiler.WordBitmap.word_bitmap_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 33 ∧
    ∀ (N n : ℕ) (ds : List ℤ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 6 = (n:ℤ) → s.ptrs 43 = (ds.length:ℤ) →
      (∀ i : Fin ds.length, s.imem (s.ptrs 3+(i.val:ℤ)) = ds[i.val]) →
      (∀ i : Fin ds.length, ∀ v : Fin n, s.ptrs 3+(i.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ)) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let result := (MinSumFPT.step P d ω)^[4*n+11*ds.length+12] (s.state 0 work)
      result.halted = true ∧ result.work = work+(4*n+11*ds.length+12) ∧
      (∀ v : Fin n, result.imem (s.ptrs 4+(v.val:ℤ)) =
        if (v.val+1:ℤ) ∈ ds then 1 else 0) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ s.ptrs 4+(v.val:ℤ)) → result.imem x = s.imem x) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∉ ([0,1,7,8,10,11,15,16] : List ℕ) → result.cfg.ptrs j = s.ptrs j) := by sorry
