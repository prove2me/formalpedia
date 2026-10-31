-- Prove2me | Theorems.Thm_ParriloTheta_theorem_6_13
-- name    : ParriloTheta.theorem_6_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:01.438077+00:00
-- url     : https://prove2.me/theorems/c89c90ec-325f-49f9-9851-0f4b778abc0f
-- title:
--   Theorem 6.13 — $H\oplus\overline{K_{\alpha-k}}$ keeps $\vartheta$-rank $1$ up to the bound (6.2)
-- statement:
--   Let $\alpha\ge k\ge2$ be integers and let $H=(V,E)$ be a graph with $\alpha(H)=k$ such that $\vartheta\text{-rank}(H\setminus i^\perp)=0$ for every node $i\in V$ and $\vartheta\text{-rank}(H)=1$. If
--   $$
--   \alpha\le\frac{k(k+3)}{k-1},\qquad(6.2)
--   $$
--   then $G=H\oplus\overline{K_{\alpha-k}}$, i.e. $H$ with $\alpha-k$ added isolated nodes, satisfies $\vartheta\text{-rank}(G)=1$.
--
--   Together with Theorem 6.6 this determines exactly how many isolated nodes such graphs tolerate.
--
--   **Formalization Note** $\overline{K_{\alpha-k}}$ is the edgeless graph on $\alpha-k$ nodes and $\oplus$ is `⊕g`; (6.2) is in $\mathbb R$.
--
--   Differences from the source:
--   - encoding: G = H ⊕ K̄_{α−k} → H ⊕g (⊥ : SimpleGraph (Fin (α − k))); reason: K̄_m is m isolated nodes; same graph
--   - encoding: a graph G = (V, E) with V = [n] → G : SimpleGraph V on a finite type V; α(G) = G.indepNum; reason: Lean convention; the same graphs up to relabelling
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Theorem 6.13, p.23 (inequality (6.2), p.20)

import Mathlib
import Definitions.Def_ParriloTheta_thetaRank
import Definitions.Def_ParriloTheta_delNbhd

namespace ParriloTheta

open SimpleGraph

/-- **Theorem 6.13: adding the maximal number of isolated nodes keeps ϑ-rank 1.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Theorem 6.13, p.23:
"Given integers α ≥ k ≥ 2, let H = (V, E) be a graph with α(H) = k and let G = H ⊕ K̄α−k. Assume
that ϑ-rank(H \ i⊥) = 0 for all i ∈ V and ϑ-rank(H) = 1. In addition assume that α, k satisfy
the inequality (6.2). Then we have ϑ-rank(G) = 1."
The inequality (6.2) (p.20) is `α ≤ k(k + 3)/(k − 1)`.

**Formalization Note.** `K̄_{α−k}` is `α − k` isolated nodes, `(⊥ : SimpleGraph (Fin (α - k)))`;
`⊕` is `⊕g`; `H \ i⊥` is `delNbhd H i`. Inequality (6.2) is in `ℝ`. -/
theorem theorem_6_13 {V : Type*} [Finite V] (H : SimpleGraph V) (α k : ℕ) (hk : 2 ≤ k)
    (hαk : k ≤ α) (hH : H.indepNum = k) (hloc : ∀ i : V, thetaRank (delNbhd H i) = 0)
    (hH1 : thetaRank H = 1) (h62 : (α : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 3) / ((k : ℝ) - 1)) :
    thetaRank (H ⊕g (⊥ : SimpleGraph (Fin (α - k)))) = 1 := by sorry

end ParriloTheta
