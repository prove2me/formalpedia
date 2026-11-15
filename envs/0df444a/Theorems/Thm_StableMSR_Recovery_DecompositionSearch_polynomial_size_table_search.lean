-- Prove2me | Theorems.Thm_StableMSR_Recovery_DecompositionSearch_polynomial_size_table_search
-- name    : StableMSR.Recovery.DecompositionSearch.polynomial_size_table_search
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T18:06:22.385411+00:00
-- url     : https://prove2.me/theorems/383dda31-392f-454a-9374-41fdb4a9cd10
-- title:
--   Exact size-ordered treewidth table with polynomial enumeration bounds
-- statement:
--   For every finite simple graph $G$ on $n$ vertices and nonnegative integer width bound $w$, the size-ordered tight-block table recognizes exactly the graphs of treewidth at most $w$. At size threshold $m$, it contains precisely the tight states $(S,C)$ with $|C|\le m$ accepted by the recurrence at depth $|C|$. The finite state universe satisfies
--
--   $$|\mathcal S|\le n(w+1)(n+1)^w.$$
--
--   Every state occurs in its unique interior-size layer. Across all $n$ layers, count one visit per state, one eligibility test per vertex subset of size at most $w+1$, and one table probe per child of each eligible bag. This explicit enumeration tally is at most
--
--   $$(w+1)(w+2)(n+1)^{2w+3}.$$
--
--   The statement includes the empty graph. It gives exact table semantics and polynomial finite-enumeration counts for fixed $w$. It does not bound the work to construct components or boundaries, implement subset enumeration and indexing, or execute the table in the charged recovery interpreter.
-- source:
--   Size-ordered tabulation of the finite tight-block recurrence; follows the proved finite_decomposition_search theorem https://prove2.me/theorems/d4f2a14a-b18f-44f7-966a-d1411797cf17 in the Exact Sum-of-Radii Clustering under Any Constant Stability mission.

import Definitions.Def_StableMSR_DecompositionSearch_Table
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
open scoped BigOperators
open StableMSR.Recovery.DecompositionSearch

theorem StableMSR.Recovery.DecompositionSearch.polynomial_size_table_search {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) :
    (sizeTableRecognizes G w ↔ RobertsonSeymour1986.GM5.TreewidthLE G w) ∧
    (searchStates G w).card ≤
      Fintype.card V * (w+1) * (Fintype.card V+1)^w ∧
    (∑ m ∈ Finset.range (Fintype.card V), ∑ p ∈ layerStates G w m,
      (1 + (smallSets (V := V) (w+1)).card +
        ∑ B ∈ candidateBags w p.1 p.2, (children G B p.2).card)) ≤
      (w+1) * (w+2) * (Fintype.card V+1)^(2*w+3) ∧
    ∀ m (S C : Finset V),
      (S,C) ∈ sizeTable G w m ↔
        (S,C) ∈ searchStates G w ∧ C.card ≤ m ∧ accepts G w C.card S C := by sorry
