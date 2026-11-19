-- Prove2me | Theorems.Thm_StrictCompatLB_FullInhomogeneous_random_graph_eventually_connected_ae
-- name    : StrictCompatLB.FullInhomogeneous.random_graph_eventually_connected_ae
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T21:16:48.041754+00:00
-- url     : https://prove2.me/theorems/0d6b44dc-a5e4-4ebb-ba82-e099fd7ffe4d
-- title:
--   The inhomogeneous random bipartite compatibility graph is almost surely eventually connected
-- statement:
--   Let $M_N\ge 1$ dispatchers and $N$ servers, where each server-dispatcher pair $(v,w)$ is an edge independently with probability $p_w(N)\in(0,1]$, and let $\bar p(N)=\min_w p_w(N)$. Assume (H.1) $N\bar p(N)/(\log M_N+\log N)\to\infty$ and (H.3) $\frac{\log N}{M_N^2}\sum_w p_w(N)^{-2}\to 0$. If the random adjacency matrices $X_N$ on a common probability space have these laws, then almost surely the bipartite compatibility graph $G_N$ is connected for all sufficiently large $N$.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Theorem 3.6 p. 14 (G_N connected for all large N, almost surely, under (H.1)-(H.3)) and Appendix B p. 35; proof: every dispatcher has a neighbour and every two servers share a dispatcher (union bound, P <= N^2 exp(-sum_w p_w^2) + M exp(-N pbar) <= 2/N^2 using Cauchy-Schwarz with (H.3) and (H.1)), then the first Borel-Cantelli lemma (R. Durrett, Probability: Theory and Examples, 5th ed., Theorem 2.3.1).

import Mathlib
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions

open MeasureTheory Filter Topology
open StrictCompatLB.MeanField StrictCompatLB.Inhomogeneous
open scoped ENNReal NNReal

namespace StrictCompatLB.FullInhomogeneous

theorem random_graph_eventually_connected_ae (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ)
    (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (h1 : Tendsto (fun N : ℕ =>
      (N : ℝ) / (Real.log (M N) + Real.log N) * minEdgeProb M p N) atTop atTop)
    (h3 : Tendsto (fun N : ℕ =>
      Real.log N / (M N : ℝ) ^ 2 * ∑ w : Fin (M N), 1 / (p N w) ^ 2) atTop (𝓝 0))
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω) [IsProbabilityMeasure P₀]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N))
    (hX_law : ∀ N, P₀.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (compatGraph M (fun N => graphOf (X N ω)) N).Connected := by sorry

end StrictCompatLB.FullInhomogeneous
