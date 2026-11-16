-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_CatalogCompose_canonical_subset_table_program
-- name    : StableMSR.Recovery.Compiler.CatalogCompose.canonical_subset_table_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-15T21:33:48.036465+00:00
-- url     : https://prove2.me/theorems/590c5a02-9a3b-4a4c-948e-3fff89969aab
-- title:
--   Canonical-input generation of all bounded-subset table keys with charged execution
-- statement:
--   For every fixed width $w\ge0$, there is a deterministic program of $7w+144$ instructions which starts with only the canonical scalar inputs $n,k$. Let $M=(n+1)^w$. The program constructs a table of $M$ records, each consisting of an $n$-cell subset key and one initialization payload. Every subset $S\subseteq\{0,\ldots,n-1\}$ of cardinality at most $w$ occurs as an exact characteristic key in this retained table, with payload zero; duplicate keys are allowed.
--
--   The table begins at integer address $2+(w+1)M+n$. At termination its base and row count are returned in the designated registers, both scalar input cells are preserved, all real registers and memory are unchanged, and no oracle query or random-tape read has occurred. The program halts within
--
--   $$(8w+6)M+M\bigl[4M+11n+11w+(M+1)(11n+16)+47\bigr]+30$$
--
--   charged instructions, including the final halt. The code is chosen before $n,k$ and the metric input; the statement includes $w=0$ and $n=0$.
--
--   This composes the bounded-word catalog generator and the full catalog-to-table sweep from the canonical input, removing the intermediate-catalog and supplied-layout hypotheses of the earlier sweep theorem. It supplies initialized subset-key records for the decomposition-search implementation. Filtering valid graph states, evaluating recurrence/DP values, deterministic geometric construction, and the complete clustering recovery program are separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; canonical-input subset-table construction supporting rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler

theorem StableMSR.Recovery.Compiler.CatalogCompose.canonical_subset_table_program (w : ℕ) :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 7*w+144 ∧
      ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
        ∃ steps ≤ (8*w+6)*(n+1)^w+(n+1)^w*(4*(n+1)^w+11*n+11*w+
          ((n+1)^w+1)*(11*n+16)+47)+30,
          let result := execute P n k d steps
          result.halted = true ∧ result.work = steps ∧
          result.queries = 0 ∧ result.tapePos = 0 ∧
          result.cfg.ptrs 5 = (((n+1)^w:ℕ):ℤ) ∧
          result.cfg.ptrs 2 = 2+((w+1)*(n+1)^w:ℕ)+(n:ℤ) ∧
          result.imem 0 = (n:ℤ) ∧ result.imem 1 = (k:ℤ) ∧
          (∀ S : Finset (Fin n), S.card ≤ w →
            ∃ a < (n+1)^w,
              (∀ v : Fin n, result.imem
                (2+((w+1)*(n+1)^w:ℕ)+(n:ℤ)+(a:ℤ)*((n:ℤ)+1)+(v.val:ℤ)) =
                  if v ∈ S then 1 else 0) ∧
              result.imem (2+((w+1)*(n+1)^w:ℕ)+(n:ℤ)+(a:ℤ)*((n:ℤ)+1)+(n:ℤ)) = 0) ∧
          result.cfg.regs = (initialStore n k).regs ∧
          result.cfg.mem = (initialStore n k).mem := by sorry
