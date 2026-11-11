-- Prove2me | Theorems.Thm_StableMSR_Recovery_small_cluster_components
-- name    : StableMSR.Recovery.small_cluster_components
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:49.170643+00:00
-- url     : https://prove2.me/theorems/d317a8e9-a283-4d7e-855b-39aeb33e04a0
-- title:
--   Lemma 3.8 — global components of small clusters
-- statement:
--   Assume $1<\gamma<2$, $k<n$, and that $\mathcal O$ is the unique optimum of a $\gamma$-stable instance. Put $\varepsilon=\gamma-1$, $R=\max_{C\in\mathcal O}r(C)$, and $b=\varepsilon R/4$. Then
--   $$
--   r(C)<b\ \Longrightarrow\ C\text{ is a connected component of the global }G_{2b}.
--   $$
--   Every other global component contains only points in large optimal clusters, whose radii are at least $b$. Singleton small clusters are included. This separates the forced small-cluster components from the components left for candidate coverage.
--
--   Differences from the source:
--   - encoding: An arbitrary finite real metric space with fixed input order and unordered clusters → Points are Fin n; clusters and unordered partitions are finite sets; metric arrays are Mathlib metric distances; reason: Relabelling preserves every finite ordered instance, all distance values, and every unordered partition
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma 3.8, p. 6; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem small_cluster_components {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O) :
    (∀ C ∈ smallClusters d O (γ - 1),
      C ∈ components d (2 * smallThreshold d O (γ - 1)) Finset.univ) ∧
    (∀ K ∈ components d (2 * smallThreshold d O (γ - 1)) Finset.univ,
      K ∉ smallClusters d O (γ - 1) → K ⊆ (largeClusters d O (γ - 1)).biUnion id) := by sorry

end StableMSR.Recovery
