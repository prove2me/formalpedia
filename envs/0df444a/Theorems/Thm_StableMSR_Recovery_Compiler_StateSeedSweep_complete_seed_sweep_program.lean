-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_StateSeedSweep_complete_seed_sweep_program
-- name    : StableMSR.Recovery.Compiler.StateSeedSweep.complete_seed_sweep_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-16T19:48:23.834232+00:00
-- url     : https://prove2.me/theorems/e8a272fa-a62b-4cbf-9f25-defde393aecd
-- title:
--   Complete charged seed sweep: exact state-table count, soundness, coverage and preservation
-- statement:
--   There is one deterministic program of $229$ instructions that, given an ordinary encoded graph $G$ on $n$ vertices, a separator bitmap $S$, width bound $w$, and an existing table with $q$ rows, scans every vertex as a seed and retains exactly the eligible component-state records. Let
--   $$C_r=\{v:\text{there is an }r\text{--}v\text{ walk in }G-S\},\qquad E=\{r\notin S:|S|\le w\text{ and }N_G(C_r)=S\}.$$
--   Here $N_G(C)$ is the external neighborhood. Given a complete sound directed arc array with $m$ entries, the actual charged interpreter halts within
--   $$n\bigl[n(17m+57)+17m+4(q+n)+116\bigr]+6$$
--   steps. Its final row count is exactly
--   $$q'=q+|E|,\qquad q\le q'\le q+n.$$
--   Every row in the new interval $[q,q')$ has key $(S,C_r)$ for some $r\in E$, and every $r\in E$ is represented by a row in that interval. Each record contains the $n$ separator bits, $n$ component bits and a zero initialization payload. Distinct seeds may give the same component, so repeated keys are allowed. Every pre-existing row is unchanged.
--
--   The separator bitmap, graph arc array, graph metadata, all real data and oracle/tape counts are preserved. The input specifies separate immutable and writable regions and room for $q+n$ records, without assumptions on initial table values or work-mask contents. The program constructs each component and boundary and decides eligibility itself; no component, boundary, state-validity certificate or output table is supplied. The code is fixed independently of all input dimensions and data. The statement includes $n=0$, width zero, oversized separators, disconnected graphs, and repeated arcs.
--
--   This supplies semantic coverage and soundness for the complete inner seed loop used to enumerate the decomposition-search states. It does not assert completion of the outer separator catalog, recurrence evaluation, geometric graph construction, or the full clustering recovery program.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Appendix A.6; implementation lemma for the tight-state enumeration specified in Decomposition_Search_Proof.md, States and recurrence, and its concrete seed loop; mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b. The instruction-level algorithm and constants are a supporting formalization, not a separately numbered claim of the paper.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.StateSeedSweep.complete_seed_sweep_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 229 ∧
    ∀ (n w q : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store),
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) → s.ptrs 43 = (w:ℤ) → s.ptrs 62 = (q:ℤ) →
      Bitmap s.imem (s.ptrs 3) S → EdgeEncoding s.imem (s.ptrs 2) es →
      Separate (n := n) (s.ptrs 3) (s.ptrs 4) →
      Separate (n := n) (s.ptrs 3) (s.ptrs 50) → Separate (n := n) (s.ptrs 3) (s.ptrs 51) →
      Separate (n := n) (s.ptrs 4) (s.ptrs 50) → Separate (n := n) (s.ptrs 50) (s.ptrs 51) →
      EdgesSeparate (s.ptrs 2) (s.ptrs 4) es → EdgesSeparate (s.ptrs 2) (s.ptrs 50) es →
      EdgesSeparate (s.ptrs 2) (s.ptrs 51) es →
      (∀ r : Fin (q+n), ∀ j : Fin (n+n+1),
        let x := s.ptrs 61+(r.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)
        (∀ v : Fin n, address (s.ptrs 3) v ≠ x ∧ address (s.ptrs 4) v ≠ x ∧
          address (s.ptrs 50) v ≠ x ∧ address (s.ptrs 51) v ≠ x) ∧
        (∀ a (ha : a < es.length), s.ptrs 2+2*(a:ℤ) ≠ x ∧ s.ptrs 2+2*(a:ℤ)+1 ≠ x)) →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ t ≤ n*(n*(17*es.length+57)+17*es.length+4*(q+n)+116)+6,
      ∃ count : ℕ, q ≤ count ∧ count ≤ q+n ∧
      let C := fun seed : Fin n => Finset.univ.filter (fun v : Fin n => ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∉ S)
      let eligible := fun seed : Fin n => seed ∉ S ∧ S.card ≤ w ∧
        S = Finset.univ.filter (fun v : Fin n => v ∉ C seed ∧ ∃ u ∈ C seed, G.Adj u v)
      let result := (MinSumFPT.step P d ω)^[t] (s.state 0 work)
      let record := fun (a : ℕ) (seed : Fin n) =>
        let base := s.ptrs 61+(a:ℤ)*((n:ℤ)+(n:ℤ)+1)
        (∀ v : Fin n, result.imem (base+(v.val:ℤ)) = if v ∈ S then 1 else 0) ∧
        (∀ v : Fin n, result.imem (base+(n:ℤ)+(v.val:ℤ)) = if v ∈ C seed then 1 else 0) ∧
        result.imem (base+(n:ℤ)+(n:ℤ)) = 0
      count = q+(Finset.univ.filter eligible).card ∧
      result.halted = true ∧ result.work = work+t ∧ result.cfg.ptrs 62 = (count:ℤ) ∧
      (∀ a : ℕ, q ≤ a → a < count → ∃ seed : Fin n, eligible seed ∧ record a seed) ∧
      (∀ seed : Fin n, eligible seed → ∃ a : ℕ, q ≤ a ∧ a < count ∧ record a seed) ∧
      (∀ a : Fin q, ∀ j : Fin (n+n+1),
        result.imem (s.ptrs 61+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)) =
          s.imem (s.ptrs 61+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ))) ∧
      Bitmap result.imem (s.ptrs 3) S ∧ EdgeEncoding result.imem (s.ptrs 2) es ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      (∀ j : ℕ, j ∈ ([2,3,4,5,6,43,50,51,61]:List ℕ) → result.cfg.ptrs j = s.ptrs j) := by sorry
