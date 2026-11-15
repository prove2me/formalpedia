-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_ComponentProgram_component_traversal_program
-- name    : StableMSR.Recovery.Compiler.ComponentProgram.component_traversal_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T20:10:36.097954+00:00
-- url     : https://prove2.me/theorems/0b6f861d-160e-4300-ac50-6b44cbb80db9
-- title:
--   A fixed charged-interpreter program for induced connected components
-- statement:
--   There is a single deterministic program with **46 instructions** that computes an induced connected component from an ordinary encoded graph input. Let $G$ be a simple graph on $n$ vertices, let $A$ be an allowed vertex set, and let $s\in A$ be a seed. The input contains a directed edge list of length $m$ representing all adjacencies in both orientations, a zero–one bitmap for $A$, the relevant array addresses and counts, and the seed index. The writable reached bitmap is disjoint from the read-only input arrays, and its initial contents are arbitrary.
--
--   The program clears the reached bitmap, marks the seed, and scans the edge array $n$ times. Its exact charged running time, including initialization, branches, loop tests, and halt, is
--
--   $$T(n,m)=n(17m+11)+15.$$
--
--   At termination, the reached cell for a vertex $v$ is exactly $1$ if there is a walk from $s$ to $v$ whose support is contained in $A$, and $0$ otherwise. Every integer cell outside this bitmap is preserved, as are all real registers and real memory, the input address/count/seed registers, the oracle-query count, and the random-tape position. The theorem holds for every oracle and tape, even when the initial work counter is nonzero.
--
--   The edge order is arbitrary and repeated arcs are allowed. For a representation with $m\le n^2$, the exact formula is at most $43n^3$ (a valid seed implies $n\ge1$). This is a verified internal component subroutine for decomposition search. Building the graph from metric input, composing the search and dynamic program, and proving the full clustering recovery program remain separate obligations. No component or solution certificate is supplied as input.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; executable graph primitive supporting rational_recovery_program (c2468a82-f9f1-431f-bb25-e0e414912c4f).

import Definitions.Def_StableMSR_ComponentGraphMemory
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.ComponentProgram.component_traversal_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 46 ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (A : Finset (Fin n)) (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store),
      GraphInput s A es seed → seed ∈ A →
      (∀ e ∈ es, G.Adj e.1 e.2) →
      (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let result := (MinSumFPT.step P d ω)^[n*(17*es.length+11)+15] (s.state 0 work)
      result.halted = true ∧ result.work = work+(n*(17*es.length+11)+15) ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      result.cfg.mem = s.mem ∧ result.cfg.regs = s.regs ∧
      (∀ v : Fin n, result.imem (address (s.ptrs 4) v) =
        if (∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∈ A) then 1 else 0) ∧
      (∀ v : Fin n, 0 < result.imem (address (s.ptrs 4) v) ↔
        ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∈ A) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 4) v) → result.imem x = s.imem x) ∧
      (∀ j : ℕ, (2 ≤ j ∧ j ≤ 6 ∨ j = 17) → result.cfg.ptrs j = s.ptrs j) := by sorry
