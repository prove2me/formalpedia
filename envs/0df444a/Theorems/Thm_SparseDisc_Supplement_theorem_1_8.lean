-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_1_8
-- name    : SparseDisc.Supplement.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:09:40.183094+00:00
-- url     : https://prove2.me/theorems/3e79a27f-e692-47a6-80f8-46d99406a688
-- title:
--   Theorem 1.8 — heavy functions with bounded ports per lobe
-- statement:
--   Fix $\Delta\ge2$. Let $F$ be a finite $t$-sparse family. If every heavy function—one meeting more than $\Delta$ bundle hyperedges—has at most $\Delta$ ports in each lobe, then
--   $$
--   \operatorname{disc}(F)\le t\Delta\max(1,2^{\Delta-2}).
--   $$
--   In particular, for $t=2$, block maximum degree at most $\Delta$ gives $\operatorname{disc}(F)\le\Delta2^{\Delta-1}$, and every cactus pattern has discrepancy at most $4$, with arbitrary degrees and bundle sizes.
--
--   Differences from the source:
--   - encoding: lobes are connected classes after deleting the heavy function and ports are incident hyperedges meeting a class → connectivity is the reflexive-transitive closure of co-membership in remaining hyperedges and ports are counted by a finite filter; reason: direct finite hypergraph encoding of Definition 7.1
--   - encoding: finite families and discrepancy inequalities → finite types and the existential colouring predicate `DiscLE`; reason: Lean convention, preserving arbitrary bundle sizes and private items
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 1.8, p.4

import Mathlib
import Definitions.Def_SparseDisc_IsOneLipschitz
import Definitions.Def_SparseDisc_DiscLE
import Definitions.Def_SparseDisc_relevant
import Definitions.Def_SparseDisc_pattern
import Definitions.Def_SparseDisc_IsTwoSparse
import Definitions.Def_SparseDisc_BlockDegreeLE
import Definitions.Def_SparseDisc_IsCactus
import Definitions.Def_SparseDisc_Supplement_IsTSparse
import Definitions.Def_SparseDisc_Supplement_PortCondition

namespace SparseDisc.Supplement

/-- **Theorem 1.8** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.4). If every heavy function has at most
`Δ` ports in each lobe, discrepancy is at most `tΔ max(1,2^(Δ-2))`; the theorem also contains
the stated block-degree and cactus consequences for `t=2`. -/
theorem theorem_1_8 :
    (∀ (t Δ : ℕ), 1 ≤ t → 2 ≤ Δ → ∀ (V ι : Type) [Fintype V]
      [DecidableEq V] [Fintype ι] [DecidableEq ι] (f : V → Finset ι → ℝ),
      (∀ v, SparseDisc.IsOneLipschitz (f v)) → IsTSparse t f →
      PortCondition (fun v => SparseDisc.relevant (f v)) Δ →
      SparseDisc.DiscLE f ((t * Δ * max 1 (2 ^ (Δ - 2)) : ℕ) : ℝ)) ∧
    (∀ (Δ : ℕ), 2 ≤ Δ → ∀ (V ι : Type) [Fintype V] [DecidableEq V]
      [Fintype ι] [DecidableEq ι] (f : V → Finset ι → ℝ),
      (∀ v, SparseDisc.IsOneLipschitz (f v)) → SparseDisc.IsTwoSparse f →
      SparseDisc.BlockDegreeLE (SparseDisc.pattern f) Δ →
      SparseDisc.DiscLE f ((Δ * 2 ^ (Δ - 1) : ℕ) : ℝ)) ∧
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (f : V → Finset ι → ℝ), (∀ v, SparseDisc.IsOneLipschitz (f v)) →
      SparseDisc.IsTwoSparse f → SparseDisc.IsCactus (SparseDisc.pattern f) →
      SparseDisc.DiscLE f 4) := by sorry

end SparseDisc.Supplement
