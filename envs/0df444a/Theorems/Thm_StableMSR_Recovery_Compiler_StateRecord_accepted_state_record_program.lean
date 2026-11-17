-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_StateRecord_accepted_state_record_program
-- name    : StableMSR.Recovery.Compiler.StateRecord.accepted_state_record_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-16T18:48:17.305244+00:00
-- url     : https://prove2.me/theorems/84769f01-ef61-459f-9fab-04cd1563a732
-- title:
--   Charged construction, filtering and retention of separator-component state records
-- statement:
--   One deterministic program of $221$ instructions constructs and tests a candidate graph-component state, then appends its exact separator-component key precisely when accepted. The ordinary input consists of a separator bitmap $S$, a complete directed arc list for an undirected graph $G$, a seed $r$, a width bound $w$, a table base and row count $q$, and writable work regions. No component bitmap, boundary bitmap, connectivity certificate, or new table record is supplied.
--
--   Let $C$ be the vertices reachable from $r$ by walks avoiding $S$, and let $B=N_G(C)$ be its external boundary. Acceptance is exactly
--
--   $$r\notin S,\qquad |S|\le w,\qquad B=S.$$
--
--   An accepted candidate appends one record consisting of the $n$ separator bits, the $n$ computed component bits, and a zero initialization payload. The new row count is $q+1$. Every old record is preserved, including when keys repeat. A rejected candidate leaves the count at $q$ and preserves both all old records and the next free record. Initial table cells and writable masks may contain arbitrary data.
--
--   For $n$ vertices and $m$ listed arcs, including repetitions, the actual charged interpreter halts within
--
--   $$n(17m+57)+17m+4q+113$$
--
--   steps, including candidate construction, the validity branches, record addressing, both key-half copies, payload write, metadata restoration and one final halt. The separator, edge array, input metadata, all real data, oracle/tape counts and cells outside the specified work regions and new record are preserved under explicit memory-separation hypotheses. The code is fixed before all input dimensions and data. Width zero, inside seeds, oversized separators and empty arc lists are included; a seed requires $n>0$.
--
--   This connects actual component-state construction to actual state-pair table writes. The payload is an initialization value. Complete table coverage across the seed and separator sweeps, recurrence/DP evaluation, graph construction from the recovery input, geometry and the full clustering recovery program remain separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Appendix A.6; implementation lemma connecting the decomposition-search recurrence in Decomposition_Search_Proof.md to concrete state-pair table writes; mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.StateRecord.accepted_state_record_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 221 ∧
    ∀ (n w q : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (S : Finset (Fin n)) (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store),
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) → s.ptrs 17 = (seed.val:ℤ) →
      s.ptrs 43 = (w:ℤ) → s.ptrs 62 = (q:ℤ) →
      Bitmap s.imem (s.ptrs 3) S → EdgeEncoding s.imem (s.ptrs 2) es →
      Separate (n := n) (s.ptrs 3) (s.ptrs 4) →
      Separate (n := n) (s.ptrs 3) (s.ptrs 50) → Separate (n := n) (s.ptrs 3) (s.ptrs 51) →
      Separate (n := n) (s.ptrs 4) (s.ptrs 50) → Separate (n := n) (s.ptrs 50) (s.ptrs 51) →
      EdgesSeparate (s.ptrs 2) (s.ptrs 4) es → EdgesSeparate (s.ptrs 2) (s.ptrs 50) es →
      EdgesSeparate (s.ptrs 2) (s.ptrs 51) es →
      (∀ r : Fin (q+1), ∀ j : Fin (n+n+1),
        let x := s.ptrs 61+(r.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)
        (∀ v : Fin n, address (s.ptrs 3) v ≠ x ∧ address (s.ptrs 4) v ≠ x ∧
          address (s.ptrs 50) v ≠ x ∧ address (s.ptrs 51) v ≠ x) ∧
        (∀ a (ha : a < es.length), s.ptrs 2+2*(a:ℤ) ≠ x ∧ s.ptrs 2+2*(a:ℤ)+1 ≠ x)) →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ t ≤ n*(17*es.length+57)+17*es.length+4*q+113,
      let C := Finset.univ.filter (fun v : Fin n => ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∉ S)
      let B := Finset.univ.filter (fun v : Fin n => v ∉ C ∧ ∃ u ∈ C, G.Adj u v)
      let accepted := seed ∉ S ∧ S.card ≤ w ∧ S = B
      let base := s.ptrs 61+(q:ℤ)*((n:ℤ)+(n:ℤ)+1)
      let result := (MinSumFPT.step P d ω)^[t] (s.state 0 work)
      result.halted = true ∧ result.work = work+t ∧
      result.cfg.ptrs 18 = (if accepted then 1 else 0) ∧
      result.cfg.ptrs 62 = ((q+(if accepted then 1 else 0):ℕ):ℤ) ∧
      (accepted →
        (∀ v : Fin n, result.imem (base+(v.val:ℤ)) = if v ∈ S then 1 else 0) ∧
        (∀ v : Fin n, result.imem (base+(n:ℤ)+(v.val:ℤ)) = if v ∈ C then 1 else 0) ∧
        result.imem (base+(n:ℤ)+(n:ℤ)) = 0) ∧
      (¬accepted → ∀ a : Fin (q+1), ∀ j : Fin (n+n+1),
        result.imem (s.ptrs 61+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 61+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ))) ∧
      (∀ a : Fin q, ∀ j : Fin (n+n+1),
        result.imem (s.ptrs 61+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 61+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ))) ∧
      Bitmap result.imem (s.ptrs 3) S ∧ EdgeEncoding result.imem (s.ptrs 2) es ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 4) v) →
        (∀ v : Fin n, x ≠ address (s.ptrs 50) v) → (∀ v : Fin n, x ≠ address (s.ptrs 51) v) →
        (x < base ∨ base+(n:ℤ)+(n:ℤ)+1 ≤ x) → result.imem x = s.imem x) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∈ ([2,3,4,5,6,17,43,50,51,61]:List ℕ) → result.cfg.ptrs j = s.ptrs j) := by sorry
