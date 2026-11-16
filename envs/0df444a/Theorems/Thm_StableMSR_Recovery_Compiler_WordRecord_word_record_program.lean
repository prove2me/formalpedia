-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_WordRecord_word_record_program
-- name    : StableMSR.Recovery.Compiler.WordRecord.word_record_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-15T18:59:20.244202+00:00
-- url     : https://prove2.me/theorems/ddafa9fd-c4d9-403e-a48d-c479ff293e8b
-- title:
--   A charged program decoding subset words, constructing records, and retrieving payloads
-- statement:
--   A single fixed deterministic program with $107$ instructions reads an ordinary integer word of length $w$, computes its decoded subset bitmap on $n$ vertices, appends that $n$-cell bitmap and a supplied payload to a table of $q$ records, and retrieves the new record by last-match lookup. The newly written key marks $v$ exactly when $v+1$ occurs in the word; padding, invalid digits, and repetitions are handled by the decoder.
--
--   The exact charged cost for this complete run, including one final halt, is
--
--   $$4q+11n+11w+(q+1)(11n+16)+43.$$
--
--   The returned row is $q$, its payload is the newly supplied value, and the updated row count is $q+1$, even when earlier rows have the same key. The original word pointer is restored. The theorem reads back every constructed key cell and the stored payload, preserves all earlier table records, and preserves every integer cell outside the bitmap workspace and the new record, together with real registers/memory and oracle/tape counts.
--
--   The word avoids the bitmap workspace, and the workspace avoids both the old table and the new record. No initial invariant is imposed on the writable bitmap or new-record contents. The result includes empty tables, empty words, and $n=0$. It establishes construction and retrieval of one subset-key record. Sweeping the entire catalog, generating all valid search states, evaluating the DP table, and proving the complete clustering recovery program remain separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; executable subset-key generation and table construction supporting rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler

theorem StableMSR.Recovery.Compiler.WordRecord.word_record_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 107 ∧
    ∀ (N n q : ℕ) (ds : List ℤ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 6 = (n:ℤ) → s.ptrs 43 = (ds.length:ℤ) → s.ptrs 5 = (q:ℤ) →
      (∀ i : Fin ds.length, s.imem (s.ptrs 3+(i.val:ℤ)) = ds[i.val]) →
      (∀ i : Fin ds.length, ∀ v : Fin n, s.ptrs 3+(i.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ)) →
      (∀ v : Fin n, ∀ j : Fin (n+1), s.ptrs 4+(v.val:ℤ) ≠
        s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) →
      (∀ i : Fin q, ∀ j : Fin (n+1), ∀ v : Fin n,
        s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ)) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let steps := 4*q+11*n+11*ds.length+(q+1)*(11*n+16)+43
      let result := (MinSumFPT.step P d ω)^[steps] (s.state 0 work)
      result.halted = true ∧ result.work = work+steps ∧
      result.cfg.ptrs 5 = ((q+1:ℕ):ℤ) ∧ result.cfg.ptrs 3 = s.ptrs 3 ∧
      result.cfg.ptrs 25 = (q:ℤ) ∧ result.cfg.ptrs 26 = s.ptrs 17 ∧
      (∀ v : Fin n, result.imem (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(v.val:ℤ)) =
        if (v.val+1:ℤ) ∈ ds then 1 else 0) ∧
      result.imem (s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(n:ℤ)) = s.ptrs 17 ∧
      (∀ i : Fin q, ∀ j : Fin (n+1),
        result.imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ))) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ s.ptrs 4+(v.val:ℤ)) →
        (x < s.ptrs 2+(q:ℤ)*((n:ℤ)+1) ∨ s.ptrs 2+(q:ℤ)*((n:ℤ)+1)+(n:ℤ)+1 ≤ x) →
        result.imem x = s.imem x) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos := by sorry
