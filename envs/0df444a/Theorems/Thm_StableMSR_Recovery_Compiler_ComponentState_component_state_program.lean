-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_ComponentState_component_state_program
-- name    : StableMSR.Recovery.Compiler.ComponentState.component_state_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-16T13:44:11.736592+00:00
-- url     : https://prove2.me/theorems/8ac82fc9-ebd1-4e50-9d1d-4399a38d2378
-- title:
--   Charged construction and exact validity test for a graph-component search state
-- statement:
--   There is one deterministic program of $161$ instructions that constructs and tests a component state from ordinary graph input: a separator bitmap $S$, a directed arc list for an undirected graph $G$, a vertex $r$, a width bound $w$, and writable workspaces. Write $n=|V(G)|$ and let $m$ be the length of the arc list. The arc list may have repetitions, and it contains every ordered adjacent pair.
--
--   Let $C$ be the vertices reachable from $r$ by a walk whose vertices avoid $S$, and let $B=N_G(C)$ be its external boundary. The program returns the exact zero-or-one acceptance flag for
--
--   $$r\notin S,\qquad |S|\le w,\qquad B=S.$$
--
--   Whenever the first two conditions hold, it constructs the characteristic bitmaps of both $C$ and $B$. It therefore derives the component itself before checking its exact boundary; no component, boundary, connectivity certificate, or state-validity answer is supplied as input. The separator bitmap is preserved. The writable masks may initially contain arbitrary data, and the statement includes empty arc lists, width zero, oversized separators, and seeds lying inside the separator. A seed vertex requires $n>0$.
--
--   The actual charged interpreter halts within
--
--   $$n(17m+43)+17m+68$$
--
--   steps, including separator counting, complement-mask construction, all traversal scans, boundary construction, comparison, rejection branches, pointer restoration, and one final halt. All real data, oracle and random-tape counts, input metadata, and integer cells outside the designated work regions are preserved under the explicit array-separation conditions. The same code is chosen before $n,m,w$ or the graph data.
--
--   This supplies the construction and filtering kernel for an individual decomposition-search state. Iterating over all catalog separators and seeds, retaining the accepted state-pair records, evaluating their recurrence/DP values, geometric construction, and the complete clustering recovery program remain separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Appendix A.6; implementation lemma for the decomposition-search recurrence in Decomposition_Search_Proof.md, supporting mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b and rational_recovery_program.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.ComponentState.component_state_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 161 ∧
    ∀ (n w : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (S : Finset (Fin n)) (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store),
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) → s.ptrs 17 = (seed.val:ℤ) →
      s.ptrs 43 = (w:ℤ) → Bitmap s.imem (s.ptrs 3) S → EdgeEncoding s.imem (s.ptrs 2) es →
      Separate (n := n) (s.ptrs 3) (s.ptrs 4) →
      Separate (n := n) (s.ptrs 3) (s.ptrs 50) → Separate (n := n) (s.ptrs 3) (s.ptrs 51) →
      Separate (n := n) (s.ptrs 4) (s.ptrs 50) → Separate (n := n) (s.ptrs 50) (s.ptrs 51) →
      EdgesSeparate (s.ptrs 2) (s.ptrs 4) es → EdgesSeparate (s.ptrs 2) (s.ptrs 50) es →
      EdgesSeparate (s.ptrs 2) (s.ptrs 51) es →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ t ≤ n*(17*es.length+43)+17*es.length+68,
      let C := Finset.univ.filter (fun v : Fin n =>
        ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∉ S)
      let B := Finset.univ.filter (fun v : Fin n => v ∉ C ∧ ∃ u ∈ C, G.Adj u v)
      let result := (MinSumFPT.step P d ω)^[t] (s.state 0 work)
      result.halted = true ∧ result.work = work+t ∧
      result.cfg.ptrs 18 = (if seed ∉ S ∧ S.card ≤ w ∧ S = B then 1 else 0) ∧
      (seed ∉ S → S.card ≤ w →
        Bitmap result.imem (s.ptrs 50) C ∧ Bitmap result.imem (s.ptrs 51) B) ∧
      Bitmap result.imem (s.ptrs 3) S ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 4) v) →
        (∀ v : Fin n, x ≠ address (s.ptrs 50) v) →
        (∀ v : Fin n, x ≠ address (s.ptrs 51) v) → result.imem x = s.imem x) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∈ ([2,3,4,5,6,17,43,50,51]:List ℕ) → result.cfg.ptrs j = s.ptrs j) := by sorry
