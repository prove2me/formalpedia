-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_Supplement_proposition_6_5
-- name    : SparseIncidenceHom.WidthComparison.Supplement.proposition_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:18:36.177355+00:00
-- url     : https://prove2.me/theorems/4440c705-5047-4b46-bf0d-51ecb0cfcae0
-- title:
--   Proposition 6.5 — heavy, connected terminal cliques force large clique embedding power
-- statement:
--   Let $C_H>0$ be a constant satisfying inequality (10) of Lemma 6.4 for every $k\ge2$ and every pseudometric on $[k]$. Let $H$ be a finite hypergraph, $\mu$ a nonnegative vertex weighting of $H$, and $K_1,\dots,K_k$ disjoint cliques of the primal graph $P(H)$ with $k\ge8$. Suppose their union is $(\mu,\lambda)$-connected for some $\lambda>0$, and $\mu(K_i)\ge1/2$ for every $i$. Then
--   $$\operatorname{emb}(H)\ge\frac{\lambda\sqrt k}{8C_H\log k}.\tag{12}$$
--
--   Combined with Lemma 6.3 this shows that unbounded submodular width forces unbounded clique embedding power (Lemma 6.2).
--
--   **Formalization Note** $\log$ is to base two. The constant $C_H$ of Lemma 6.4 enters only through inequality (10), so the statement is made for every positive constant satisfying (10).
--
--   Differences from the source:
--   - generalization: the hypergraph H is nonempty and connected (p. 7 standing convention) → H is any finite hypergraph (published FiniteHypergraph), possibly empty or disconnected; reason: on nonempty connected H the Lean statement is the source's
--   - reading: C_H, the constant of Lemma 6.4 → any C_H > 0 satisfying inequality (10); reason: the source refers to "the" constant of Lemma 6.4, which is any constant for which (10) holds; the proof uses only (10)
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 26, Proposition 6.5 (inequality (12)); proof pp. 26–27

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Supplement_Widths

namespace SparseIncidenceHom.WidthComparison.Supplement

open SparseIncidenceHom.WidthComparison

/-- Lanzinger, STOC 2027 submission #662, Proposition 6.5, p. 26 (inequality (12)). `C_H` is any
positive constant for which inequality (10) of Lemma 6.4 holds. -/
theorem proposition_6_5 (C_H : ℝ) (hC : 0 < C_H) (hhub : HubBound C_H)
    (V : Type) [Fintype V] (H : FiniteHypergraph V) (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (k : ℕ) (hk : 8 ≤ k) (K : Fin k → Finset V)
    (hclique : ∀ i, (primal H).IsClique (K i : Set V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (lam : ℝ) (hlam : 0 < lam) (hconn : IsMuLambdaConnected H μ lam (⋃ i, (K i : Set V)))
    (hmass : ∀ i, (1 : ℝ) / 2 ≤ weightOf μ (K i)) :
    lam * Real.sqrt (k : ℝ) / (8 * C_H * logTwo (k : ℝ)) ≤ cliqueEmbeddingPower H := by sorry

end SparseIncidenceHom.WidthComparison.Supplement
