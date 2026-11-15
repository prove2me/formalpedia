-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_TightBoundaryProgram_tight_boundary_program
-- name    : StableMSR.Recovery.Compiler.TightBoundaryProgram.tight_boundary_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-15T01:31:12.399018+00:00
-- url     : https://prove2.me/theorems/6f502243-66ed-4559-bc44-050c2dcfc98e
-- title:
--   A charged program deciding the tight-boundary equality
-- statement:
--   There is one deterministic program with $61$ instructions that constructs the external boundary of a set $C$ and decides whether it equals a supplied candidate set $S$. Its input is an ordinary directed edge array of length $m$ for a simple graph on $n$ vertices, characteristic bitmaps for $C$ and $S$, and a separate writable boundary bitmap. The edge representation is sound and complete in both orientations; order and duplicates are unrestricted.
--
--   The program clears and constructs
--
--   $$N_G(C)=\{v\notin C:\exists u\in C,\;G(u,v)\},$$
--
--   then compares its actual bitmap against the supplied bitmap for $S$. It returns the canonical flag $1$ exactly when $S=N_G(C)$ and $0$ otherwise, preserving the constructed boundary bitmap. The entire composed run, including pointer redirection/restoration and one halt, costs exactly
--
--   $$15n+17m+21$$
--
--   charged interpreter steps. The source, candidate, and edge arrays must be separate from the writable output, whose initial contents are unrestricted. All integer memory outside the boundary bitmap, all real registers and memory, original input addresses/dimensions, and oracle/tape counts are preserved. Empty graphs and empty sets are covered. The equality is decided by actual instructions, rather than supplied as a certificate. This verifies the tight-boundary comparison used by decomposition search; it does not by itself test the other conditions for a valid search state or implement the whole recovery algorithm.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; executable comparisons and state-table lookup supporting rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
import Mathlib.Combinatorics.SimpleGraph.Basic
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.TightBoundaryProgram.tight_boundary_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 61 ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (C S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store),
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) →
      Bitmap s.imem (s.ptrs 3) C → Bitmap s.imem (s.ptrs 17) S →
      EdgeEncoding s.imem (s.ptrs 2) es →
      Separate (n := n) (s.ptrs 3) (s.ptrs 4) →
      Separate (n := n) (s.ptrs 17) (s.ptrs 4) →
      EdgesSeparate (s.ptrs 2) (s.ptrs 4) es →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let B := Finset.univ.filter (fun v : Fin n => v ∉ C ∧ ∃ u ∈ C, G.Adj u v)
      let result := (MinSumFPT.step P d ω)^[15*n+17*es.length+21] (s.state 0 work)
      result.halted = true ∧ result.work = work+(15*n+17*es.length+21) ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      result.cfg.mem = s.mem ∧ result.cfg.regs = s.regs ∧
      result.cfg.ptrs 18 = (if S = B then 1 else 0) ∧
      (result.cfg.ptrs 18 = 1 ↔ S = B) ∧
      (∀ v : Fin n, result.imem (address (s.ptrs 4) v) =
        if v ∉ C ∧ (∃ u ∈ C, G.Adj u v) then 1 else 0) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 4) v) → result.imem x = s.imem x) ∧
      (∀ j : ℕ, (2 ≤ j ∧ j ≤ 6 ∨ j = 17) → result.cfg.ptrs j = s.ptrs j) := by sorry
