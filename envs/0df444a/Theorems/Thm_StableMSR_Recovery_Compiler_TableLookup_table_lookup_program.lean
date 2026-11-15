-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_TableLookup_table_lookup_program
-- name    : StableMSR.Recovery.Compiler.TableLookup.table_lookup_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-15T01:33:06.773632+00:00
-- url     : https://prove2.me/theorems/a4475977-3719-4615-8dc7-ac7dbb8f18fa
-- title:
--   A fixed charged program for variable-width key-table lookup
-- statement:
--   One deterministic program with $46$ instructions searches an ordinary integer-memory table containing $q$ consecutive records. Each record contains an $L$-cell integer key followed by one integer payload. The query is another $L$-cell array. The program initializes its result and scans the records in order, comparing every key against the query.
--
--   It halts after exactly
--
--   $$q(11L+16)+12$$
--
--   charged interpreter steps. If no key matches, the returned index is the sentinel $q$ and the payload is $0$. Otherwise it returns the greatest index of a matching record and that record's actual stored payload. In particular a uniquely matching key retrieves its record. Duplicate keys have defined behavior: the last matching record wins.
--
--   The result includes empty tables, zero-length keys, arbitrary integer entries, arbitrary initial output registers, and arbitrary initial work counters. For zero-length keys every record matches, so a nonempty table returns its last payload. All memory is read-only, and the query/table addresses, dimensions, real registers, oracle-query count, and tape position are preserved. The program and its finite instruction count are independent of $q$ and $L$. The theorem supplies a concrete lookup primitive for state tables; construction and population of those tables remain separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; executable comparisons and state-table lookup supporting rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
import Mathlib.Combinatorics.SimpleGraph.Basic
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.TableLookup.table_lookup_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 46 ∧
    ∀ (N q L : ℕ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 5 = (q : ℤ) → s.ptrs 6 = (L : ℤ) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let result := (MinSumFPT.step P d ω)^[q*(11*L+16)+12] (s.state 0 work)
      result.halted = true ∧ result.work = work+(q*(11*L+16)+12) ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      result.cfg.mem = s.mem ∧ result.cfg.regs = s.regs ∧ result.imem = s.imem ∧
      (result.cfg.ptrs 25 = (q : ℤ) ↔
        ∀ i : Fin q, ¬ (∀ j : Fin L, s.imem (s.ptrs 3+(j.val : ℤ)) =
          s.imem (s.ptrs 2+(i.val : ℤ)*((L : ℤ)+1)+(j.val : ℤ)))) ∧
      (result.cfg.ptrs 25 = (q : ℤ) → result.cfg.ptrs 26 = 0) ∧
      (result.cfg.ptrs 25 ≠ (q : ℤ) →
        ∃ i : Fin q, result.cfg.ptrs 25 = (i.val : ℤ) ∧
          (∀ j : Fin L, s.imem (s.ptrs 3+(j.val : ℤ)) =
            s.imem (s.ptrs 2+(i.val : ℤ)*((L : ℤ)+1)+(j.val : ℤ))) ∧
          result.cfg.ptrs 26 = s.imem (s.ptrs 2+(i.val : ℤ)*((L : ℤ)+1)+(L : ℤ)) ∧
          ∀ k : Fin q, (∀ j : Fin L, s.imem (s.ptrs 3+(j.val : ℤ)) =
            s.imem (s.ptrs 2+(k.val : ℤ)*((L : ℤ)+1)+(j.val : ℤ))) →
              k.val ≤ i.val) ∧
      (0 ≤ result.cfg.ptrs 25 ∧ result.cfg.ptrs 25 ≤ (q : ℤ)) ∧
      (∀ j : ℕ, j ∉ ([0,4,18,20,21,22,23,24,25,26,27,28,29,30,32] : List ℕ) →
        result.cfg.ptrs j = s.ptrs j) := by sorry
