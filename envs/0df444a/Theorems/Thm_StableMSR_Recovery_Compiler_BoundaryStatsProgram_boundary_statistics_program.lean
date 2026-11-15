-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_BoundaryStatsProgram_boundary_statistics_program
-- name    : StableMSR.Recovery.Compiler.BoundaryStatsProgram.boundary_statistics_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T21:00:14.546478+00:00
-- url     : https://prove2.me/theorems/8120ceb6-a622-4119-901d-7d4166f29302
-- title:
--   A charged program for external boundaries, cardinalities, and least vertices
-- statement:
--   There is a single deterministic program with $58$ instructions that computes the external neighborhood of a vertex set, its cardinality, and its least vertex from ordinary graph data. For a simple graph $G$ on $n$ vertices and a set $C$, write
--
--   $$B=N_G(C)=\{v\notin C:\exists u\in C,\;G(u,v)\}.$$
--
--   The input consists of a zero–one bitmap for $C$ and a directed edge list of length $m$ containing exactly graph adjacencies, with every adjacency represented in both orientations. The writable output bitmap is disjoint from these input arrays; its initial contents are arbitrary. Edge order and duplicates are unrestricted.
--
--   The program initializes the output bitmap, scans the edge array to compute $B$, and scans the resulting bitmap for its cardinality and least vertex. The entire composed program, including pointer redirection/restoration and one final halt, takes exactly
--
--   $$13n+17m+22$$
--
--   charged interpreter steps. The output bitmap is exactly the characteristic function of $B$. Register $18$ contains $|B|$, while register $19$ contains its least vertex or the sentinel $n$ exactly when $B$ is empty. The initial graph pointers and dimensions, all integer cells outside the output bitmap, all real registers and memory, and oracle/tape counts are preserved.
--
--   The result covers $n=0$, empty boundaries, and arbitrary initial output contents and work counters. This supplies concrete boundary construction and size/representative extraction for decomposition search. It does not assume a precomputed boundary, implement subset ranking or bitmap comparison, or establish the full clustering recovery program.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability; Prove2Me mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b; executable tight-boundary construction supporting rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
import Mathlib.Combinatorics.SimpleGraph.Basic
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.BoundaryStatsProgram.boundary_statistics_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 58 ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (C : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store),
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) →
      Bitmap s.imem (s.ptrs 3) C → EdgeEncoding s.imem (s.ptrs 2) es →
      Separate (n := n) (s.ptrs 3) (s.ptrs 4) →
      EdgesSeparate (s.ptrs 2) (s.ptrs 4) es →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let B := Finset.univ.filter (fun v : Fin n => v ∉ C ∧ ∃ u ∈ C, G.Adj u v)
      let result := (MinSumFPT.step P d ω)^[13*n+17*es.length+22] (s.state 0 work)
      result.halted = true ∧ result.work = work+(13*n+17*es.length+22) ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      result.cfg.mem = s.mem ∧ result.cfg.regs = s.regs ∧
      (∀ v : Fin n, result.imem (address (s.ptrs 4) v) =
        if v ∉ C ∧ (∃ u ∈ C, G.Adj u v) then 1 else 0) ∧
      result.cfg.ptrs 18 = (B.card:ℤ) ∧
      (result.cfg.ptrs 19 = (n:ℤ) ↔ B = ∅) ∧
      (B.Nonempty → ∃ v ∈ B, result.cfg.ptrs 19 = (v.val:ℤ) ∧
        ∀ u ∈ B, v.val ≤ u.val) ∧
      (0 ≤ result.cfg.ptrs 19 ∧ result.cfg.ptrs 19 ≤ (n:ℤ)) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 4) v) → result.imem x = s.imem x) ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ 6 → result.cfg.ptrs j = s.ptrs j) := by sorry
