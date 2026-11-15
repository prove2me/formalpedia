-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_TableAppend_table_append_program
-- name    : StableMSR.Recovery.Compiler.TableAppend.table_append_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-15T02:58:00.849067+00:00
-- url     : https://prove2.me/theorems/acf0bc19-3356-437a-8653-b51f8cd051d1
-- title:
--   A fixed charged program constructing an appended key/payload record
-- statement:
--   A single deterministic program with $27$ instructions appends a key/payload record to an ordinary integer-memory table. The input consists of a table base address, row count $q$, key width $L$, an $L$-cell source key, and a payload in an integer register. Existing records contain $L$ key cells followed by one payload cell.
--
--   The program computes the next record address using additions, copies the key, writes the payload, and increments the row count. It halts after exactly
--
--   $$4q+7L+18$$
--
--   charged interpreter steps, including all address calculations, loads, stores, loop tests, and halt. Every cell of every earlier record is preserved. Outside the new $L+1$ record cells, all integer memory is preserved, as are all real registers/memory, the table and source-key addresses, the width, payload register, and oracle/tape counts.
--
--   The source key must be disjoint from the new record's writable cells; it may lie in the older table. New-record cells and scratch registers initially contain arbitrary values. No preconstructed new record is supplied. Empty tables and zero-width keys are covered. This is a concrete record-construction primitive for the finite search table, with table generation and the full recovery algorithm remaining separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; concrete table construction and updates supporting rational_recovery_program.

import Definitions.Def_StableMSR_StructuredCompiler
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler

theorem StableMSR.Recovery.Compiler.TableAppend.table_append_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 27 ∧
    ∀ (N q L : ℕ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 5 = (q:ℤ) → s.ptrs 6 = (L:ℤ) →
      (∀ i : Fin L, ∀ j : Fin (L+1), s.ptrs 3+(i.val:ℤ) ≠
        s.ptrs 2+(q:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let base := s.ptrs 2+(q:ℤ)*((L:ℤ)+1)
      let result := (MinSumFPT.step P d ω)^[4*q+7*L+18] (s.state 0 work)
      result.halted = true ∧ result.work = work+(4*q+7*L+18) ∧
      result.cfg.ptrs 5 = ((q+1:ℕ):ℤ) ∧
      (∀ i : Fin L, result.imem (base+(i.val:ℤ)) = s.imem (s.ptrs 3+(i.val:ℤ))) ∧
      result.imem (base+(L:ℤ)) = s.ptrs 17 ∧
      (∀ i : Fin q, ∀ j : Fin (L+1),
        result.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ))) ∧
      (∀ x : ℤ, x < base ∨ base+(L:ℤ)+1 ≤ x → result.imem x = s.imem x) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∉ ([4,5,34,35,36,37,38,39,40,41] : List ℕ) →
        result.cfg.ptrs j = s.ptrs j) := by sorry
