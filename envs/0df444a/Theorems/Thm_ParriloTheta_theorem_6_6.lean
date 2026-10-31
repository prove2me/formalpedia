-- Prove2me | Theorems.Thm_ParriloTheta_theorem_6_6
-- name    : ParriloTheta.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:30:56.756984+00:00
-- url     : https://prove2.me/theorems/ee12c9d8-f1f3-495e-b90e-5a12328292be
-- title:
--   Theorem 6.6 — $\alpha\le k(k+3)/(k-1)$ when $H\oplus\overline{K_{\alpha-k}}$ has $\vartheta$-rank $1$
-- statement:
--   Let $\alpha>k\ge2$ be integers and let $H=(V,E)$ be a graph with $\alpha(H)=k$ whose subgraph of critical edges $H_c=(V,E_c)$ is connected. Let $G=H\oplus\overline{K_{\alpha-k}}$ be $H$ together with $\alpha-k$ isolated nodes. If $\vartheta\text{-rank}(G)=1$, then
--   $$
--   \alpha\le\frac{k(k+3)}{k-1}=k+4+\frac{4}{k-1}.\qquad(6.2)
--   $$
--   So at most $4+4/(k-1)$ isolated nodes can be added to such a graph while keeping $\vartheta$-rank $1$.
--
--   **Formalization Note** $\overline{K_{\alpha-k}}$ is the edgeless graph on $\alpha-k$ nodes and $\oplus$ the disjoint union `⊕g`. Both displayed relations are stated, in $\mathbb R$.
--
--   Differences from the source:
--   - encoding: G = H ⊕ K̄_{α−k} → H ⊕g (⊥ : SimpleGraph (Fin (α − k))) on V ⊕ Fin (α − k); reason: K̄_m is m isolated nodes; same graph
--   - encoding: a graph G = (V, E) with V = [n] → G : SimpleGraph V on a finite type V; α(G) = G.indepNum; reason: Lean convention; the same graphs up to relabelling
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Theorem 6.6 with eq. (6.2), p.20

import Mathlib
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical
import Definitions.Def_ParriloTheta_thetaRank

namespace ParriloTheta

open ChvatalPolytopes.Separation SimpleGraph

/-- **Theorem 6.6: an upper bound on the number of isolated nodes.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Theorem 6.6 with eq. (6.2), p.20:
"Given integers α > k ≥ 2, let H = (V, E) be a graph with α(H) = k and let G = H ⊕ K̄α−k. Assume
the graph Hc = (V, Ec) is connected and ϑ-rank(G) = 1. Then we have
α ≤ k(k + 3)/(k − 1) = k + 4 + 4/(k − 1). (6.2)"

**Formalization Note.** `K̄_{α−k}` (the overline is the complement of the complete graph) is
`α − k` isolated nodes, `(⊥ : SimpleGraph (Fin (α - k)))`; `⊕` is the disjoint union `⊕g` on
`V ⊕ Fin (α − k)`. `H_c` is the published `criticalGraph H`. Both displayed relations of (6.2)
are stated, in `ℝ`. -/
theorem theorem_6_6 {V : Type*} [Finite V] (H : SimpleGraph V) (α k : ℕ) (hk : 2 ≤ k)
    (hαk : k < α) (hH : H.indepNum = k) (hc : (criticalGraph H).Connected)
    (hG : thetaRank (H ⊕g (⊥ : SimpleGraph (Fin (α - k)))) = 1) :
    (α : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 3) / ((k : ℝ) - 1) ∧
      (k : ℝ) * ((k : ℝ) + 3) / ((k : ℝ) - 1) = (k : ℝ) + 4 + 4 / ((k : ℝ) - 1) := by sorry

end ParriloTheta
