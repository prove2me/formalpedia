-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_8_35
-- name    : SparseDisc.Supplement.theorem_8_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:14:55.460647+00:00
-- url     : https://prove2.me/theorems/8f5e3c9b-58fe-41dc-a750-35b73218e2d2
-- title:
--   Theorem 8.35 — leveled bases, peeling and seven-vertex exceptions
-- statement:
--   Let $(G,\ell)$ be a finite leveled graph with no adjacent level-$1$ vertices. It is good if $G$ has at most five vertices, or if $G$ has six vertices of which at most two have level $1$. Consequently every $2$-sparse family of eight functions has discrepancy at most $3$.
--
--   Every $2$-sparse family has discrepancy at most $2$ if its pattern can be reduced to at most six vertices by repeatedly deleting a vertex with at most two current neighbours. The same bound holds for a seven-vertex pattern unless it is one of the eight graphs $K_7-E(F)$ with $F$ isomorphic to a subgraph of $C_4$, $3K_2$, or $K_3$.
--
--   Differences from the source:
--   - encoding: repeated deletion of vertices with at most two current neighbours → an injective deletion rank and a residual set of at most six vertices, with each deleted vertex having at most two later or residual neighbours; reason: exact finite encoding of a peeling sequence
--   - encoding: $K_7-E(F)$ with $F$ isomorphic to a subgraph of $C_4$, $3K_2$, or $K_3$ → graph difference from the complete graph and an injective edge-preserving map on the non-isolated vertices of $F$ into one of those three targets; reason: isolated vertices are suppressed in the paper's isomorphism convention
--   - encoding: families with eight or seven functions → finite function types of cardinality exactly eight or seven; reason: Lean convention, same finite families
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.35, p.45

import Mathlib
import Definitions.Def_SparseDisc_IsLevelGood
import Definitions.Def_SparseDisc_IsOneLipschitz
import Definitions.Def_SparseDisc_IsTwoSparse
import Definitions.Def_SparseDisc_DiscLE
import Definitions.Def_SparseDisc_pattern
import Definitions.Def_SparseDisc_Supplement_PeelsToAtMost
import Definitions.Def_SparseDisc_Supplement_IsSevenException

namespace SparseDisc.Supplement

open Classical in
/-- **Theorem 8.35** (computer-assisted; Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond
Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.45). The full
leveled bases, eight-function bound, peeling criterion, and exact seven-vertex exception
classification are included.

**Formalization Note** `PeelsToAtMost G 6` records an actual repeated deletion order, with each
deleted vertex having at most two neighbours in the then-current graph. `IsSevenException` is
exactly `K₇-E(F)` with the edge-bearing part of `F` embeddable in `C₄`, `3K₂`, or `K₃`. -/
theorem theorem_8_35 :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ℓ : V → ℕ),
      (∀ v, 1 ≤ ℓ v) → (∀ u v, G.Adj u v → ¬ (ℓ u = 1 ∧ ℓ v = 1)) →
      (Fintype.card V ≤ 5 ∨
        (Fintype.card V = 6 ∧ (Finset.univ.filter (fun v => ℓ v = 1)).card ≤ 2)) →
      SparseDisc.IsLevelGood G ℓ) ∧
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (f : V → Finset ι → ℝ), Fintype.card V = 8 →
      (∀ v, SparseDisc.IsOneLipschitz (f v)) → SparseDisc.IsTwoSparse f →
      SparseDisc.DiscLE f 3) ∧
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (f : V → Finset ι → ℝ), (∀ v, SparseDisc.IsOneLipschitz (f v)) →
      SparseDisc.IsTwoSparse f → PeelsToAtMost (SparseDisc.pattern f) 6 →
      SparseDisc.DiscLE f 2) ∧
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (f : V → Finset ι → ℝ), Fintype.card V = 7 →
      (∀ v, SparseDisc.IsOneLipschitz (f v)) → SparseDisc.IsTwoSparse f →
      ¬ IsSevenException (SparseDisc.pattern f) → SparseDisc.DiscLE f 2) := by sorry

end SparseDisc.Supplement
