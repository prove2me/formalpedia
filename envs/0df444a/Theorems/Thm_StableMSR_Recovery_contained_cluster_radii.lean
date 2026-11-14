-- Prove2me | Theorems.Thm_StableMSR_Recovery_contained_cluster_radii
-- name    : StableMSR.Recovery.contained_cluster_radii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:24.040191+00:00
-- url     : https://prove2.me/theorems/a810f075-5bbe-4e8c-8137-bcee42978bba
-- title:
--   Lemma 3.2 — radii of clusters contained in a ball
-- statement:
--   Let $d$ be any finite real metric, $1\le k\le n$, and $\mathcal O$ any optimal exact-$k$ partition. For every $x\in P$ and $s\ge0$,
--   $$
--   \sum_{C\in\mathcal O:\ C\subseteq B(x,s)}r(C)\le s.
--   $$
--   The sum concerns all clusters contained in the closed ball, including an empty subfamily. The center $x$ need not belong to their union. This gives the ordinary-optimality bound used in local density and candidate ownership.
--
--   Differences from the source:
--   - encoding: An arbitrary finite real metric space with fixed input order and unordered clusters → Points are Fin n; clusters and unordered partitions are finite sets; metric arrays are Mathlib metric distances; reason: Relabelling preserves every finite ordered instance, all distance values, and every unordered partition
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma 3.2, p. 5; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem contained_cluster_radii {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (O : Partition n) (hO : Optimal d Finset.univ k O) (x : Point n)
    (s : ℝ) (hs : 0 ≤ s) :
    (∑ C ∈ O.filter (fun C => C ⊆ ball d x s), radius d C) ≤ s := by sorry

end StableMSR.Recovery
