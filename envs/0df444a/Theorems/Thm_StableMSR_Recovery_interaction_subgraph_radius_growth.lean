-- Prove2me | Theorems.Thm_StableMSR_Recovery_interaction_subgraph_radius_growth
-- name    : StableMSR.Recovery.interaction_subgraph_radius_growth
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T14:48:02.166073+00:00
-- url     : https://prove2.me/theorems/9b5a0328-6f41-4403-b836-8e1e66c13f5c
-- title:
--   Lemma 4.4: linear growth of the local interaction graph
-- statement:
--   Consider a $\gamma$-stable MSR instance with $1<\gamma<2$ and $1\le k<n$, and put $\varepsilon=\gamma-1$. Let $R$ be the largest optimal radius and $\rho=\varepsilon M/4$, where $M$ is the sum of the large-cluster radii. Let $W$ have diameter at most $\rho$, and let $N\subseteq W$ be strictly $2R$-separated. Join net points whose metric distance is at most $8R$.
--
--   Let $H$ be any nonempty subgraph with vertices in $N$. If there is a vertex $x\in H$ from which every vertex of $H$ is reachable by a walk of length at most an integer $j\ge1$ entirely inside $H$, then
--   $$|V(H)|\le\left(1+\frac{80}{\varepsilon}+\frac{80}{\varepsilon^2}\right)j.$$
--
--   This proves the linear-growth input in Lemma 4.4, with graph radius measured inside the subgraph. Applying Campbell's treewidth theorem is a separate obligation. Alignment of $W$ and maximality of the separated net are not needed for this growth estimate.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Section 4.3, Lemma 4.4, density-to-linear-growth portion of the proof; Lemma 3.9; Table 2 for the growth constant.

import Definitions.Def_StableMSR_Recovery_Geometry
import Definitions.Def_StableMSR_Recovery_Parameters

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem interaction_subgraph_radius_growth {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O)
    (W N : Cluster n) (hNW : N ⊆ W)
    (hdiam : diameter d W ≤ densityScale d O (γ - 1))
    (hsep : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → 2 * largestRadius d O < d a b)
    (H : (thresholdGraph d (8 * largestRadius d O) N).Subgraph)
    (hHN : H.verts ⊆ (N : Set (Point n)))
    (x : H.verts) (j : ℕ) (hj : 1 ≤ j)
    (hwalk : ∀ y : H.verts, ∃ p : H.coe.Walk x y, p.length ≤ j) :
    ((Finset.univ.filter (fun y => y ∈ H.verts)).card : ℝ) ≤
      growthConstant (γ - 1) * (j : ℝ) := by sorry

end StableMSR.Recovery
