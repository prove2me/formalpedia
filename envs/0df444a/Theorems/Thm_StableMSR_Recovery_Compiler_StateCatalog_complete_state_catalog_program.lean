-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_StateCatalog_complete_state_catalog_program
-- name    : StableMSR.Recovery.Compiler.StateCatalog.complete_state_catalog_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-17T00:09:00.736972+00:00
-- url     : https://prove2.me/theorems/29180d12-6d91-4983-a916-abcdfc19421d
-- title:
--   Complete charged separator-catalog and seed enumeration into state records
-- statement:
--   One deterministic program of $239$ instructions constructs the component-state table for an entire encoded separator catalog. Let $G$ be a simple graph on $n$ vertices, represented by a sound complete directed arc array with $m$ entries. Let $S_0,\ldots,S_{M-1}$ be separator bitmaps stored with stride $n+1$, and let $q$ existing state records precede the new output. Repeated separators and repeated arcs are allowed. For each catalog position define
--   $$C_{i,r}=\{v:\text{an }r\text{--}v\text{ walk in }G\text{ avoids }S_i\},\qquad E_i=\{r\notin S_i:|S_i|\le w,\ N_G(C_{i,r})=S_i\}.$$
--   Here $N_G(C)$ denotes the external neighborhood. Under explicit separation of input bitmap cells, graph cells, writable work regions and the reserved state-table region, the actual interpreter halts within
--   $$M\Bigl[n\bigl(n(17m+57)+17m+4(q+Mn)+116\bigr)+9\Bigr]+8$$
--   charged steps. The final count satisfies
--   $$q'=q+\sum_{i=0}^{M-1}|E_i|,\qquad q\le q'\le q+Mn.$$
--   Every new row represents $(S_i,C_{i,r})$ for an eligible pair $(i,r)$, and every eligible pair has a surviving row. A record consists of both $n$-bit characteristic vectors and a zero initialization payload. Every old record, every input separator bitmap, the graph arc array, the relevant graph/table metadata, all real data and oracle/tape counts are preserved.
--
--   The nested program constructs and tests each component and its boundary, then conditionally writes its record. No component, boundary, validity flag, constructed state record, or recurrence answer is an input. The code is fixed before all dimensions and data; $M=0$, $n=0$, width zero, oversized separators, duplicate keys and arbitrary initial table/workspace contents are covered. No claim of distinctness is made: the exact count is by eligible catalog-position/seed pairs.
--
--   This is the complete outer separator loop composed with the complete inner seed sweep. For a catalog covering all subsets of size at most $w$, its records cover every tight decomposition-search state. The bitmap catalog and graph are ordinary intermediate inputs; composing their generation with this loop under a derived layout, computing recurrence values and witnesses, geometry, and the end-to-end clustering recovery theorem remain separate tasks.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Appendix A.6; supporting implementation lemma for tight-state enumeration in Decomposition_Search_Proof.md, States and recurrence, using the already verified subset-key catalog and seed sweep. Mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b. The concrete instruction-level algorithm and constants are supporting formalization details, not a numbered theorem of the paper.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.StateCatalog.complete_state_catalog_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 239 ∧
    ∀ (n w q M : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (Ss : ℕ → Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store),
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) → s.ptrs 43 = (w:ℤ) →
      s.ptrs 62 = (q:ℤ) → s.ptrs 72 = (M:ℤ) → EdgeEncoding s.imem (s.ptrs 2) es →
      (∀ i < M,
        let base := s.ptrs 3+(i:ℤ)*((n:ℤ)+1)
        Bitmap s.imem base (Ss i) ∧ Separate (n := n) base (s.ptrs 4) ∧
        Separate (n := n) base (s.ptrs 50) ∧ Separate (n := n) base (s.ptrs 51) ∧
        (∀ r : Fin (q+M*n), ∀ j : Fin (n+n+1), ∀ v : Fin n,
          address base v ≠ s.ptrs 61+(r.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ))) →
      Separate (n := n) (s.ptrs 4) (s.ptrs 50) → Separate (n := n) (s.ptrs 50) (s.ptrs 51) →
      EdgesSeparate (s.ptrs 2) (s.ptrs 4) es → EdgesSeparate (s.ptrs 2) (s.ptrs 50) es →
      EdgesSeparate (s.ptrs 2) (s.ptrs 51) es →
      (∀ r : Fin (q+M*n), ∀ j : Fin (n+n+1),
        let x := s.ptrs 61+(r.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)
        (∀ v : Fin n, address (s.ptrs 4) v ≠ x ∧ address (s.ptrs 50) v ≠ x ∧ address (s.ptrs 51) v ≠ x) ∧
        (∀ a (ha : a < es.length), s.ptrs 2+2*(a:ℤ) ≠ x ∧ s.ptrs 2+2*(a:ℤ)+1 ≠ x)) →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ t ≤ M*(n*(n*(17*es.length+57)+17*es.length+4*(q+M*n)+116)+9)+8,
      ∃ count : ℕ, q ≤ count ∧ count ≤ q+M*n ∧
      let C := fun (i : ℕ) (seed : Fin n) => Finset.univ.filter
        (fun v : Fin n => ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∉ Ss i)
      let eligible := fun (i : ℕ) (seed : Fin n) => seed ∉ Ss i ∧ (Ss i).card ≤ w ∧
        Ss i = Finset.univ.filter (fun v : Fin n => v ∉ C i seed ∧ ∃ u ∈ C i seed, G.Adj u v)
      let result := (MinSumFPT.step P d ω)^[t] (s.state 0 work)
      let record := fun (a i : ℕ) (seed : Fin n) =>
        let base := s.ptrs 61+(a:ℤ)*((n:ℤ)+(n:ℤ)+1)
        (∀ v : Fin n, result.imem (base+(v.val:ℤ)) = if v ∈ Ss i then 1 else 0) ∧
        (∀ v : Fin n, result.imem (base+(n:ℤ)+(v.val:ℤ)) = if v ∈ C i seed then 1 else 0) ∧
        result.imem (base+(n:ℤ)+(n:ℤ)) = 0
      count = q+∑ i ∈ Finset.range M, (Finset.univ.filter (eligible i)).card ∧
      result.halted = true ∧ result.work = work+t ∧ result.cfg.ptrs 62 = (count:ℤ) ∧
      (∀ a : ℕ, q ≤ a → a < count → ∃ i < M, ∃ seed : Fin n, eligible i seed ∧ record a i seed) ∧
      (∀ i < M, ∀ seed : Fin n, eligible i seed → ∃ a : ℕ, q ≤ a ∧ a < count ∧ record a i seed) ∧
      (∀ a : Fin q, ∀ j : Fin (n+n+1),
        result.imem (s.ptrs 61+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 61+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ))) ∧
      (∀ i < M, Bitmap result.imem (s.ptrs 3+(i:ℤ)*((n:ℤ)+1)) (Ss i)) ∧
      EdgeEncoding result.imem (s.ptrs 2) es ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∈ ([2,4,5,6,43,50,51,61]:List ℕ) → result.cfg.ptrs j = s.ptrs j) := by sorry
