-- Prove2me | Theorems.Thm_StrictCompatLB_Inhomogeneous_random_inhomogeneous_sparse_subcritical
-- name    : StrictCompatLB.Inhomogeneous.random_inhomogeneous_sparse_subcritical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:10.136379+00:00
-- url     : https://prove2.me/theorems/8e4e68f6-e21f-4f1a-9ea9-8b885d57c7f6
-- title:
--   Theorem 3.6 — inhomogeneous random compatibility graphs satisfying (3.5) are a.s. proportionally sparse and subcritical
-- statement:
--   Let $d \ge 2$ be the JSQ($d$) sampling size and $M(N) \ge 1$ the number of dispatchers. For each $N$ let $p_w(N) \in (0, 1]$, $w \in W_N$, be edge probabilities satisfying, as $N \to \infty$,
--   $$\text{(1)}\ \ \frac{N}{\ln M(N) + \ln N}\, \min_{w \in W_N} p_w(N) \to \infty, \qquad \text{(2)}\ \ M(N) \min_{w \in W_N} p_w(N) \to \infty, \qquad \text{(3)}\ \ \frac{\ln N}{M(N)^2} \sum_{w \in W_N} \frac{1}{p_w(N)^2} \to 0. \qquad (3.5)$$
--   On a probability space $(\Omega, \mathcal F, \mathbb P)$ let $G_N$, $N \ge 1$, be random bipartite graphs on $V_N \times W_N$ ($|V_N| = N$, $|W_N| = M(N)$) built by selecting each edge $(v, w)$ independently with probability $p_w(N)$; nothing is assumed about the joint law of graphs with different $N$. Then, almost surely, the sequence $\{G_N\}_{N \ge 1}$ is proportionally sparse (Definition 3.1) and satisfies the subcriticality condition (Definition 3.3).
--
--   The theorem gives a random construction of sparse compatibility graphs with dispatcher-dependent flexibility under which, by the paper's Theorem 3.4, JSQ($d$) has the same mean-field limit and steady state as in the fully flexible system.
--
--   **Formalization Note** The graphs are given through measurable random adjacency matrices $X_N$ whose law is the product of Bernoulli$(p_w(N))$ laws; the conditions $p_w(N) \in (0, 1]$ and $M(N) \ge 1$ are implicit in the paper. At $N = 1$ the denominator $\ln M(N) + \ln N$ can vanish (Lean's $x/0 = 0$), which affects finitely many $N$ and no limit. Proportional sparsity is the limit condition (3.1) without connectivity, and subcriticality is the repaired Definition 3.3 (see the definition item). Only the graph part is stated: the closing sentence "Consequently, the conclusions of Theorem 3.4 hold" composes this result with Theorem 3.4 and is not part of this statement.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 14, Theorem 3.6

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph

open MeasureTheory Filter Topology

namespace StrictCompatLB.Inhomogeneous

/-- Theorem 3.6, graph part (p. 14): if the edge probabilities `p_w(N) ∈ (0, 1]` satisfy (3.5),
the inhomogeneous random bipartite compatibility graphs `G_N` (edge `(v, w)` present independently
with probability `p_w(N)`) are almost surely proportionally sparse and satisfy the subcriticality
condition for JSQ(`d`). Only the law of each `G_N` is prescribed (no assumption on the joint law
across `N`). -/
theorem random_inhomogeneous_sparse_subcritical (d : ℕ) (hd : 2 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ) (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (h1 : Tendsto (fun N : ℕ =>
      (N : ℝ) / (Real.log (M N) + Real.log N) * minEdgeProb M p N) atTop atTop)
    (h2 : Tendsto (fun N : ℕ => (M N : ℝ) * minEdgeProb M p N) atTop atTop)
    (h3 : Tendsto (fun N : ℕ =>
      Real.log N / (M N : ℝ) ^ 2 * ∑ w : Fin (M N), 1 / (p N w) ^ 2) atTop (𝓝 0))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N)) (hX_law : ∀ N, P.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsPropSparse M (fun N => graphOf (X N ω)) ∧
      StrictCompatLB.MeanField.IsSubcritical d M (fun N => graphOf (X N ω)) := by sorry

end StrictCompatLB.Inhomogeneous
