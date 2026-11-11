-- Prove2me | Theorems.Thm_StableMSR_Recovery_local_cluster_density
-- name    : StableMSR.Recovery.local_cluster_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:40.03287+00:00
-- url     : https://prove2.me/theorems/1c9a401a-0573-47e4-8797-546d23e96dd6
-- title:
--   Lemma 3.9 — local cluster density
-- statement:
--   Assume $1<\gamma<2$, $k<n$, and a $\gamma$-stable instance with optimum $\mathcal O$. Write $\varepsilon=\gamma-1$, $R=\max_Cr(C)$, $b=\varepsilon R/4$, $\mathcal T=\{C:r(C)\ge b\}$, $t=|\mathcal T|$, $M=\sum_{C\in\mathcal T}r(C)$, and $\rho=\varepsilon M/4$.
--
--   1. Every union of at least $t+1$ small optimal clusters has radius greater than $\varepsilon M$.
--   2. For every $x\in P$ and $0\le u\le\rho$,
--   $$
--   |\{C\text{ small}:C\cap B(x,u)\ne\varnothing\}|\le1+\frac{2u+2b}{\varepsilon b}.
--   $$
--   3. For every $x\in P$ and $u\ge0$,
--   $$
--   |\{C\in\mathcal T:C\cap B(x,u)\ne\varnothing\}|\le\frac{u+2R}{b}.
--   $$
--   All three clauses are retained, and only the small-cluster counting bound has the threshold $u\le\rho$. These bounds supply the density input for the partition and treewidth arguments.
--
--   Differences from the source:
--   - encoding: An arbitrary finite real metric space with fixed input order and unordered clusters → Points are Fin n; clusters and unordered partitions are finite sets; metric arrays are Mathlib metric distances; reason: Relabelling preserves every finite ordered instance, all distance values, and every unordered partition
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma 3.9, p. 7; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem local_cluster_density {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O) :
    (∀ F : Partition n, F ⊆ smallClusters d O (γ - 1) →
      (largeClusters d O (γ - 1)).card + 1 ≤ F.card →
      (γ - 1) * largeMass d O (γ - 1) < radius d (F.biUnion id)) ∧
    (∀ x : Point n, ∀ u : ℝ, 0 ≤ u → u ≤ densityScale d O (γ - 1) →
      ((meeting (smallClusters d O (γ - 1)) (ball d x u)).card : ℝ) ≤
        1 + (2 * u + 2 * smallThreshold d O (γ - 1)) /
          ((γ - 1) * smallThreshold d O (γ - 1))) ∧
    (∀ x : Point n, ∀ u : ℝ, 0 ≤ u →
      ((meeting (largeClusters d O (γ - 1)) (ball d x u)).card : ℝ) ≤
        (u + 2 * largestRadius d O) / smallThreshold d O (γ - 1)) := by sorry

end StableMSR.Recovery
