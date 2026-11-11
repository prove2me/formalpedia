-- Prove2me | Theorems.Thm_StableMSR_Recovery_optimum_restriction
-- name    : StableMSR.Recovery.optimum_restriction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:34.127656+00:00
-- url     : https://prove2.me/theorems/17c474ce-22f0-4ff0-bb7b-c274f8b32421
-- title:
--   Lemma 3.4 — restriction of the unique optimum
-- statement:
--   Let $\mathcal O$ be the unique optimal exact-$k$ partition in an arbitrary finite metric. If $W$ is a nonempty union of its whole clusters, let $\mathcal O|_W$ denote those clusters and $j=|\mathcal O|_W|$. Then
--   $$
--   \mathcal O|_W\text{ is the unique optimal exact-}j\text{ partition of }W.
--   $$
--   Stability is not required. Centers remain inside their own clusters. This is the uniqueness statement needed to identify a feasible local table entry with the restricted global optimum.
--
--   Differences from the source:
--   - encoding: An arbitrary finite real metric space with fixed input order and unordered clusters → Points are Fin n; clusters and unordered partitions are finite sets; metric arrays are Mathlib metric distances; reason: Relabelling preserves every finite ordered instance, all distance values, and every unordered partition
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma 3.4, p. 5; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem optimum_restriction {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (O : Partition n) (hO : UniqueOptimal d Finset.univ k O)
    (W : Cluster n) (hW : W.Nonempty) (halign : Aligned O W) :
    UniqueOptimal d W (restrictPartition O W).card (restrictPartition O W) := by sorry

end StableMSR.Recovery
