-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P09_compactIffMarginalsCompact
-- name    : QAlgorithms.Papers.Independent.Frontier18.P09.compactIffMarginalsCompact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:59:21.511232+00:00
-- url     : https://prove2.me/theorems/9a13e362-3253-42f0-91d5-1fc8e72d1c32
-- title:
--   Compactness of bipartite states from both marginal sets
-- statement:
--   Let $\mathcal H_A$ and $\mathcal H_B$ be nonzero separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-class operators of trace one on $\mathcal H$, equipped with the trace-norm topology. Let $S\subseteq\mathfrak S(\mathcal H_A\otimes\mathcal H_B)$ be closed, and put $S_A=\{\operatorname{Tr}_B\omega:\omega\in S\}$ and $S_B=\{\operatorname{Tr}_A\omega:\omega\in S\}$. Then
--
--   $$
--   S\text{ is compact}\quad\Longleftrightarrow\quad S_A\text{ and }S_B\text{ are compact}.
--   $$
--
--   This criterion transfers compactness questions to the two marginal state spaces. The empty set is permitted.
--
--   **Formalization Note** Countable nonempty orthonormal coordinate sets describe all such Hilbert spaces; arbitrary nuclear density arrays and their trace-norm topology are reused from the pinned accepted library. Partial traces are computed by summing diagonal blocks.
-- source:
--   Squashed entanglement in infinite dimensions, arXiv:1507.08964v5, PDF p. 4, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier18.P09

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize)

/-- Lemma 1, arXiv:1507.08964v5, PDF p.4: a closed set of bipartite
states is compact exactly when both sets of marginals are compact. All three
state spaces carry the accepted trace-norm topology. The empty set is allowed. -/
theorem compactIffMarginalsCompact {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (S : Set (State (I × J))) (hclosed : IsClosed S) :
    IsCompact S ↔ IsCompact (marginalStatesA S) ∧
      IsCompact (marginalStatesB S) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P09

end
