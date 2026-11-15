-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_TableAppendLookup_table_append_lookup_program
-- name    : StableMSR.Recovery.Compiler.TableAppendLookup.table_append_lookup_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-15T02:57:56.36138+00:00
-- url     : https://prove2.me/theorems/c4b5ac22-7f12-4c76-a347-a356218f3713
-- title:
--   A charged append-and-lookup program realizing latest-record updates
-- statement:
--   There is one fixed deterministic program with $72$ instructions that constructs a new key/payload record and retrieves it in the same charged interpreter run. Given an ordinary table with $q$ records of $L$ key cells plus one integer payload, a source key, and a new payload, it computes the append address, copies the key, writes the new payload, increments the row count, and runs the verified last-match lookup on the enlarged table.
--
--   Its exact charged running time, including both phases and one final halt, is
--
--   $$4q+7L+(q+1)(11L+16)+29.$$
--
--   The returned index is $q$ and the returned payload is the new payload. This holds even if older records have the same key: the newly written record takes precedence. The theorem also reads back every copied key cell and the actual stored payload, proves preservation of every earlier record, and frames all integer memory outside the new record. Real registers/memory, the original table/source/width/payload inputs, and oracle/tape counts are preserved.
--
--   The source key must be separate from the writable new record; all new cells and scratch registers start arbitrarily. The proof covers $q=0$ and $L=0$. The code is chosen before the dimensions, table data, and oracle. This supplies a concrete append-based update with verified retrieval; generating and populating the full decomposition-search table and composing the complete clustering recovery program remain separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; concrete table construction and updates supporting rational_recovery_program.

import Definitions.Def_StableMSR_StructuredCompiler
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler

theorem StableMSR.Recovery.Compiler.TableAppendLookup.table_append_lookup_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 72 ∧
    ∀ (N q L : ℕ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 5 = (q:ℤ) → s.ptrs 6 = (L:ℤ) →
      (∀ i : Fin L, ∀ j : Fin (L+1), s.ptrs 3+(i.val:ℤ) ≠
        s.ptrs 2+(q:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let base := s.ptrs 2+(q:ℤ)*((L:ℤ)+1)
      let steps := 4*q+7*L+(q+1)*(11*L+16)+29
      let result := (MinSumFPT.step P d ω)^[steps] (s.state 0 work)
      result.halted = true ∧ result.work = work+steps ∧
      result.cfg.ptrs 5 = ((q+1:ℕ):ℤ) ∧
      result.cfg.ptrs 25 = (q:ℤ) ∧ result.cfg.ptrs 26 = s.ptrs 17 ∧
      (∀ i : Fin L, result.imem (base+(i.val:ℤ)) = s.imem (s.ptrs 3+(i.val:ℤ))) ∧
      result.imem (base+(L:ℤ)) = s.ptrs 17 ∧
      (∀ i : Fin q, ∀ j : Fin (L+1),
        result.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ))) ∧
      (∀ x : ℤ, x < base ∨ base+(L:ℤ)+1 ≤ x → result.imem x = s.imem x) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∉ ([0,4,5,18,20,21,22,23,24,25,26,27,28,29,30,32,
        34,35,36,37,38,39,40,41] : List ℕ) → result.cfg.ptrs j = s.ptrs j) := by sorry
