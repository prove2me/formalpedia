-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_Supplement_lemma_6_3
-- name    : SparseIncidenceHom.WidthComparison.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:17:38.682883+00:00
-- url     : https://prove2.me/theorems/ab42daf4-9709-403f-8a46-561ad2a63b5f
-- title:
--   Lemma 6.3 — high submodular width yields many heavy, highly connected primal cliques
-- statement:
--   There are absolute constants $\beta,c_T,w_0>0$ such that every finite hypergraph $H$ with $w=\operatorname{subw}(H)\ge w_0$ admits a nonnegative vertex weighting $\mu$ and disjoint nonempty cliques $K_1,\dots,K_k$ of the primal graph $P(H)$ such that
--   $$k\ge c_T\sqrt w,\qquad \mu(K_i)\ge\tfrac12\quad(i\in[k]),$$
--   and $\bigcup_{i=1}^kK_i$ is $(\mu,\beta)$-connected.
--
--   The constants are fixed before the hypergraph. This is the consequence of Marx's results that starts the passage from submodular width to clique embeddings.
--
--   **Formalization Note** $\mu(X)=\sum_{v\in X}\mu(v)$; $(\mu,\beta)$-connectivity uses fractional $(X,Y)$-separators of hyperedges, as in the definition item `SparseIncidenceHom.WidthComparison.Supplement.Widths`. The weighting is only required to be nonnegative, as printed.
--
--   Differences from the source:
--   - generalization: the hypergraph H is nonempty and connected (p. 7 standing convention) → H is any finite hypergraph (published FiniteHypergraph), possibly empty or disconnected; reason: on nonempty connected H the Lean statement is the source's
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 24, Lemma 6.3 (consequence of [Mar13, Theorem 5.1 and Lemma 6.5]); proof p. 24

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Supplement_Widths

namespace SparseIncidenceHom.WidthComparison.Supplement

open SparseIncidenceHom.WidthComparison

/-- Lanzinger, STOC 2027 submission #662, Lemma 6.3, p. 24. The constants precede every
hypergraph. Cliques are cliques of the primal graph `P(H)`. -/
theorem lemma_6_3 :
    ∃ β cT w₀ : ℝ, 0 < β ∧ 0 < cT ∧ 0 < w₀ ∧
      ∀ (V : Type) [Fintype V] (H : FiniteHypergraph V), w₀ ≤ submodularWidth H →
        ∃ μ : V → ℝ, (∀ v, 0 ≤ μ v) ∧
          ∃ (k : ℕ) (K : Fin k → Finset V),
            (∀ i, (K i).Nonempty) ∧ (∀ i, (primal H).IsClique (K i : Set V)) ∧
            (∀ i j, i ≠ j → Disjoint (K i) (K j)) ∧
            cT * Real.sqrt (submodularWidth H) ≤ (k : ℝ) ∧
            (∀ i, (1 : ℝ) / 2 ≤ weightOf μ (K i)) ∧
            IsMuLambdaConnected H μ β (⋃ i, (K i : Set V)) := by sorry

end SparseIncidenceHom.WidthComparison.Supplement
