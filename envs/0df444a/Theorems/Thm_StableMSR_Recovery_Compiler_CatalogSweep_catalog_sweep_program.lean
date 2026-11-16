-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_CatalogSweep_catalog_sweep_program
-- name    : StableMSR.Recovery.Compiler.CatalogSweep.catalog_sweep_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-15T21:08:10.569756+00:00
-- url     : https://prove2.me/theorems/2587ac37-8bb2-4d8a-a8d1-c95bf7f511b0
-- title:
--   A fixed charged program constructing a table from every catalog entry
-- statement:
--   A single deterministic program with $119$ instructions consumes a finite catalog of $M$ integer words of fixed width $w$ and appends every decoded subset key to an ordinary table. Vertex $v$ is present in a word's key exactly when that word contains digit $v+1$. Zero is padding, invalid digits are ignored, and duplicate words or decoded subsets are allowed. Each word occupies $w$ data cells, with one intervening spacer cell between entries, matching the earlier headed catalog layout.
--
--   Starting with $q$ existing table records, the program iterates the verified decode/append/lookup command, restores the reusable bitmap workspace, advances the catalog cursor, and updates the row count. At termination, row $q+a$ contains exactly the characteristic bitmap decoded from catalog entry $a$, followed by the supplied initialization payload. The row count is $q+M$ and the source cursor advances by $M(w+1)$.
--
--   Every source-word cell, every old table record, all real registers and memory, and oracle/tape counts are preserved. Integer cells outside the bitmap workspace and newly appended records are unchanged. The catalog, bitmap workspace, and full table region are separate in the stated ordinary-memory representation. No new record or computed bitmap is supplied as advice. The theorem includes empty catalogs, zero-width words, $n=0$, and arbitrary initial writable cells.
--
--   The actual interpreter halts within
--
--   $$M\bigl[4(q+M)+11n+11w+(q+M+1)(11n+16)+47\bigr]+9$$
--
--   charged steps, including every repeated comparison, record write, loop test, and the final halt. The code is fixed before all dimensions and catalog contents. This completes a catalog-to-table loop on an encoded intermediate input; composing it with the catalog generator from canonical inputs and evaluating the search/DP records remain separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; full catalog-to-table construction supporting rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler

theorem StableMSR.Recovery.Compiler.CatalogSweep.catalog_sweep_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 119 ∧
    ∀ (N n w q : ℕ) (ws : List (Fin w → ℤ)) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 6 = (n:ℤ) → s.ptrs 43 = (w:ℤ) → s.ptrs 5 = (q:ℤ) →
      s.ptrs 48 = (ws.length:ℤ) →
      (∀ a : Fin ws.length, ∀ i : Fin w,
        s.imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ)) = ws[a.val] i) →
      (∀ a : Fin ws.length, ∀ i : Fin w, ∀ v : Fin n,
        s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) ≠ s.ptrs 4+(v.val:ℤ)) →
      (∀ a : Fin ws.length, ∀ i : Fin w, ∀ r : Fin (q+ws.length), ∀ j : Fin (n+1),
        s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ) ≠ s.ptrs 2+(r.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) →
      (∀ v : Fin n, ∀ r : Fin (q+ws.length), ∀ j : Fin (n+1),
        s.ptrs 4+(v.val:ℤ) ≠ s.ptrs 2+(r.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ steps ≤ ws.length*(4*(q+ws.length)+11*n+11*w+
        (q+ws.length+1)*(11*n+16)+47)+9,
      let result := (MinSumFPT.step P d ω)^[steps] (s.state 0 work)
      result.halted = true ∧ result.work = work+steps ∧
      result.cfg.ptrs 5 = ((q+ws.length:ℕ):ℤ) ∧
      result.cfg.ptrs 3 = s.ptrs 3+(ws.length:ℤ)*((w:ℤ)+1) ∧
      (∀ a : Fin ws.length,
        (∀ v : Fin n, result.imem (s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(v.val:ℤ)) =
          if ∃ i : Fin w, ws[a.val] i = (v.val+1:ℤ) then 1 else 0) ∧
        result.imem (s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(n:ℤ)) = s.ptrs 17) ∧
      (∀ i : Fin q, ∀ j : Fin (n+1),
        result.imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 2+(i.val:ℤ)*((n:ℤ)+1)+(j.val:ℤ))) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ s.ptrs 4+(v.val:ℤ)) →
        (∀ a : Fin ws.length, ∀ j : Fin (n+1),
          x ≠ s.ptrs 2+((q+a.val:ℕ):ℤ)*((n:ℤ)+1)+(j.val:ℤ)) → result.imem x = s.imem x) ∧
      (∀ a : Fin ws.length, ∀ i : Fin w,
        result.imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ)) =
          s.imem (s.ptrs 3+(a.val:ℤ)*((w:ℤ)+1)+(i.val:ℤ))) ∧
      result.cfg.ptrs 2 = s.ptrs 2 ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos := by sorry
