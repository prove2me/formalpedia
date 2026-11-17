-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_1_6
-- name    : SparseDisc.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:08:51.79782+00:00
-- url     : https://prove2.me/theorems/17f47298-8c4f-4d23-98da-8fe415f0ec5e
-- title:
--   Theorem 1.6 — bundle-degree discrepancy bound
-- statement:
--   Let $F$ be a finite $t$-sparse family. For each bundle hyperedge $e$, let
--   $$
--   k_e=\sum_{v\in e}\max(1,2^{d_v-2}),\qquad \Delta=\max_v d_v,
--   $$
--   where $d_v$ is the number of bundle hyperedges containing $v$. After discarding functions with no non-private hyperedge as in the source's standing paragraph,
--   $$
--   \operatorname{disc}(F)\le \max_v\sum_{e\ni v}k_e
--     \le t\Delta\max(1,2^{\Delta-2}).
--   $$
--   If $t=2$ and $\Delta\ge2$, then $\operatorname{disc}(F)\le\Delta2^{\Delta-1}$. If the underlying simple graph is a cycle, with arbitrary bundle sizes and private items, then $\operatorname{disc}(F)\le4$.
--
--   Differences from the source:
--   - encoding: the pre-theorem convention discards functions of bundle degree zero and says $d_v\ge1$ → the main Lean clause explicitly assumes $1\le d_v$ for every indexed function; reason: makes the section's standing convention binding and prevents a private-only function from making the displayed maximum zero
--   - encoding: finite families, hyperedges, sums and maxima → finite types and `Finset` sums/suprema; reason: Lean convention, with exactly the paper's finite bundle hypergraph
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 1.6, pp.3–4

import Mathlib
import Definitions.Def_SparseDisc_IsOneLipschitz
import Definitions.Def_SparseDisc_DiscLE
import Definitions.Def_SparseDisc_relevant
import Definitions.Def_SparseDisc_pattern
import Definitions.Def_SparseDisc_IsCycle
import Definitions.Def_SparseDisc_IsTwoSparse
import Definitions.Def_SparseDisc_Supplement_IsTSparse
import Definitions.Def_SparseDisc_Supplement_bundleEdges

namespace SparseDisc.Supplement

open Classical in
/-- **Theorem 1.6** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), pp.3–4). For bundle-hypergraph degrees
`d_v`, put `k_e = ∑_{v∈e} max(1,2^(d_v-2))`. The discrepancy is bounded by the maximum
incident `k_e`-sum, itself at most `t Δ max(1,2^(Δ-2))`; the full `t=2` and cycle consequences
are included.

**Formalization Note** The source's paragraph immediately before the theorem discards functions
that meet no non-private hyperedge and then says `d_v ≥ 1`; the first clause states that standing
condition explicitly. Natural subtraction in the exponent is harmless under `1 ≤ d_v` because
`max(1,·)` gives the source value for `d_v=1`. -/
theorem theorem_1_6 :
    (∀ (t : ℕ), 1 ≤ t → ∀ (V ι : Type) [Fintype V] [DecidableEq V]
      [Fintype ι] [DecidableEq ι] (f : V → Finset ι → ℝ),
      (∀ v, SparseDisc.IsOneLipschitz (f v)) → IsTSparse t f →
      let U := fun v => SparseDisc.relevant (f v)
      let E := bundleEdges U
      let d := fun v => (E.filter (fun e => v ∈ e)).card
      let k := fun e => ∑ v ∈ e, max 1 (2 ^ (d v - 2))
      let load := fun v => ∑ e ∈ E.filter (fun e => v ∈ e), k e
      let Δ := Finset.univ.sup d
      (∀ v, 1 ≤ d v) →
        SparseDisc.DiscLE f ((Finset.univ.sup load : ℕ) : ℝ) ∧
        Finset.univ.sup load ≤ t * Δ * max 1 (2 ^ (Δ - 2))) ∧
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (f : V → Finset ι → ℝ), (∀ v, SparseDisc.IsOneLipschitz (f v)) →
      SparseDisc.IsTwoSparse f →
      let U := fun v => SparseDisc.relevant (f v)
      let E := bundleEdges U
      let d := fun v => (E.filter (fun e => v ∈ e)).card
      let Δ := Finset.univ.sup d
      2 ≤ Δ → SparseDisc.DiscLE f ((Δ * 2 ^ (Δ - 1) : ℕ) : ℝ)) ∧
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (f : V → Finset ι → ℝ), (∀ v, SparseDisc.IsOneLipschitz (f v)) →
      SparseDisc.IsTwoSparse f → SparseDisc.IsCycle (SparseDisc.pattern f) →
      SparseDisc.DiscLE f 4) := by sorry

end SparseDisc.Supplement
