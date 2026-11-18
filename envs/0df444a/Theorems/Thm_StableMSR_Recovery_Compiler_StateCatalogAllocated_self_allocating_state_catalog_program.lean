-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_StateCatalogAllocated_self_allocating_state_catalog_program
-- name    : StableMSR.Recovery.Compiler.StateCatalogAllocated.self_allocating_state_catalog_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-17T10:43:36.707856+00:00
-- url     : https://prove2.me/theorems/b8ed99d5-b5eb-45dd-b5d3-40dd1ff9eac5
-- title:
--   Self-allocating construction of the complete component-state catalog
-- statement:
--   There is one fixed deterministic program of $260$ instructions which allocates its own work regions and constructs all eligible component-state records from adjacent encoded graph and separator arrays. Let $G$ have $n$ vertices and a sound complete directed arc array of length $m$, starting at an arbitrary integer address $b$. Let $M$ separator bitmaps $S_i$ immediately follow the $2m$ endpoint cells, each with stride $n+1$. Width $w$, vertex/arc/catalog counts and the two input base pointers are ordinary inputs. No workspace or table base pointer, zeroed mask, initial output record or separation certificate is supplied.
--
--   For each catalog position define
--   $$C_{i,r}=\{v:\text{an }r\text{--}v\text{ walk avoids }S_i\},\qquad E_i=\{r\notin S_i:|S_i|\le w,\ N_G(C_{i,r})=S_i\}.$$
--   The program computes the table address
--   $$B=b+2m+M(n+1)+3n$$
--   and halts with exactly
--   $$q'=\sum_{i=0}^{M-1}|E_i|\le Mn$$
--   records at that address. Each record contains the two $n$-bit characteristic vectors for $(S_i,C_{i,r})$ and a zero initialization payload. Every new row has an eligible position/seed witness, and every eligible position/seed pair is represented. Duplicate keys are permitted. The graph encoding, every input separator bitmap, real data and oracle/tape counts are preserved.
--
--   Including allocation, every traversal and validity branch, both loop levels, all conditional table writes and one halt, the actual charged interpreter runs within
--   $$M\Bigl[n\bigl(n(17m+57)+17m+4Mn+116\bigr)+13\Bigr]+26$$
--   steps. The three workspaces occupy the $3n$ cells following the catalog. Arbitrary initial memory values are permitted; $M=0$, $n=0$, width zero, oversized separators, repeated catalog entries and repeated arcs are included. The graph and bitmap catalog remain ordinary encoded intermediate inputs. Generating those arrays from the recovery input, evaluating recurrence payloads, reconstructing witnesses, geometry and full clustering recovery remain separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Appendix A.6; supporting implementation lemma for the tight-state enumeration in Decomposition_Search_Proof.md, complete outer separator enumeration and contiguous layout. The concrete allocation algorithm and constants are supporting formalization, not a separately numbered paper theorem. Mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.StateCatalogAllocated.self_allocating_state_catalog_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 260 ∧
    ∀ (n w M : ℕ) (b : ℤ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (Ss : ℕ → Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store),
      s.ptrs 2 = b → s.ptrs 3 = b+2*(es.length:ℤ) →
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) → s.ptrs 43 = (w:ℤ) → s.ptrs 72 = (M:ℤ) →
      EdgeEncoding s.imem b es →
      (∀ i < M, Bitmap s.imem (b+2*(es.length:ℤ)+(i:ℤ)*((n:ℤ)+1)) (Ss i)) →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ t ≤ M*(n*(n*(17*es.length+57)+17*es.length+4*(M*n)+116)+13)+26,
      ∃ count : ℕ, count ≤ M*n ∧
      let C := fun (i : ℕ) (seed : Fin n) => Finset.univ.filter
        (fun v : Fin n => ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∉ Ss i)
      let eligible := fun (i : ℕ) (seed : Fin n) => seed ∉ Ss i ∧ (Ss i).card ≤ w ∧
        Ss i = Finset.univ.filter (fun v : Fin n => v ∉ C i seed ∧ ∃ u ∈ C i seed, G.Adj u v)
      let result := (MinSumFPT.step P d ω)^[t] (s.state 0 work)
      let table := b+2*(es.length:ℤ)+(M:ℤ)*((n:ℤ)+1)+3*(n:ℤ)
      let record := fun (a i : ℕ) (seed : Fin n) =>
        let base := table+(a:ℤ)*((n:ℤ)+(n:ℤ)+1)
        (∀ v : Fin n, result.imem (base+(v.val:ℤ)) = if v ∈ Ss i then 1 else 0) ∧
        (∀ v : Fin n, result.imem (base+(n:ℤ)+(v.val:ℤ)) = if v ∈ C i seed then 1 else 0) ∧
        result.imem (base+(n:ℤ)+(n:ℤ)) = 0
      count = ∑ i ∈ Finset.range M, (Finset.univ.filter (eligible i)).card ∧
      result.halted = true ∧ result.work = work+t ∧ result.cfg.ptrs 62 = (count:ℤ) ∧
      result.cfg.ptrs 61 = table ∧
      (∀ a : ℕ, a < count → ∃ i < M, ∃ seed : Fin n, eligible i seed ∧ record a i seed) ∧
      (∀ i < M, ∀ seed : Fin n, eligible i seed → ∃ a : ℕ, a < count ∧ record a i seed) ∧
      (∀ i < M, Bitmap result.imem (b+2*(es.length:ℤ)+(i:ℤ)*((n:ℤ)+1)) (Ss i)) ∧
      EdgeEncoding result.imem b es ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos := by sorry
