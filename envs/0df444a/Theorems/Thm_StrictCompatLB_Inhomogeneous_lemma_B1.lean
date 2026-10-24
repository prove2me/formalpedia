-- Prove2me | Theorems.Thm_StrictCompatLB_Inhomogeneous_lemma_B1
-- name    : StrictCompatLB.Inhomogeneous.lemma_B1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:07.933181+00:00
-- url     : https://prove2.me/theorems/637f480f-be11-4c4e-bfd1-29466cae270f
-- title:
--   Lemma B.1 — inhomogeneous random graphs with $N\bar p(N) \to \infty$ and $M(N)\bar p(N) \to \infty$ are a.s. proportionally sparse
-- statement:
--   Let $M(N) \ge 1$ and let $p_w(N) \in (0, 1]$, $w \in W_N$, be edge probabilities. On a probability space $(\Omega, \mathcal F, \mathbb P)$ let $G_N$, $N \ge 1$, be random bipartite graphs on $V_N \times W_N$ ($|V_N| = N$, $|W_N| = M(N)$) such that, for each $N$, the edges of $G_N$ are present independently, $(v, w)$ with probability $p_w(N)$. Nothing is assumed about the joint law of graphs with different $N$. Write $\bar p(N) = \min_{w \in W_N} p_w(N)$. If
--   $$N \bar p(N) \to \infty \qquad\text{and}\qquad M(N)\, \bar p(N) \to \infty \qquad (N \to \infty),$$
--   that is, $\bar p(N) = \omega(1/N)$ and $\bar p(N) = \omega(1/M(N))$, then almost surely the sequence $\{G_N\}_{N \ge 1}$ is proportionally sparse.
--
--   This is the proportional-sparsity half of Theorem 3.6. Its hypotheses follow from conditions (1) and (2) of (3.5).
--
--   **Formalization Note** The graphs are given through random adjacency matrices $X_N : \Omega \to \{0,1\}^{V_N \times W_N}$, which are measurable and whose law is the product of the Bernoulli$(p_w(N))$ laws. The condition $p_w(N) \in (0, 1]$ is implicit in the paper. Proportional sparsity is the limit condition (3.1) alone, without connectivity: these random graphs are disconnected with positive probability for every $N$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 35, Lemma B.1

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph

open MeasureTheory Filter Topology

namespace StrictCompatLB.Inhomogeneous

/-- Lemma B.1 (p. 35): if `p̄(N) = ω(1/N)` and `p̄(N) = ω(1/M(N))`, the inhomogeneous random
bipartite graphs with edge probabilities `p_w(N)` are almost surely proportionally sparse. Only the
law of each `G_N` is prescribed (no assumption on the joint law across `N`). -/
theorem lemma_B1 (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ) (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (hN : Tendsto (fun N : ℕ => (N : ℝ) * minEdgeProb M p N) atTop atTop)
    (hMp : Tendsto (fun N : ℕ => (M N : ℝ) * minEdgeProb M p N) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N)) (hX_law : ∀ N, P.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsPropSparse M (fun N => graphOf (X N ω)) := by sorry

end StrictCompatLB.Inhomogeneous
