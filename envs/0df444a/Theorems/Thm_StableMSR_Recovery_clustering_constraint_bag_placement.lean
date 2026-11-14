-- Prove2me | Theorems.Thm_StableMSR_Recovery_clustering_constraint_bag_placement
-- name    : StableMSR.Recovery.clustering_constraint_bag_placement
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T16:12:22.306364+00:00
-- url     : https://prove2.me/theorems/68a60618-bad2-4ab5-9f1f-3ff29a6be119
-- title:
--   Appendix A.6: clustering constraint supports lie in decomposition bags
-- statement:
--   Let $d$ be a finite metric, let $R\ge0$, and let each candidate set $C_i$ lie within distance $R$ of its specified center $c_i$. Assign it to an owner $v_i\in N$ with $d(v_i,c_i)\le2R$. The interaction graph on $N$ joins distinct vertices at distance at most $8R$. Fix any finite tree decomposition of that graph.
--
--   Every point constraint fits in a single bag: for each input point $x$, some bag contains all owners of candidates covering $x$.
--
--   Every optional-component constraint also fits in a single bag: if an optional set $K$ has diameter at most $2R$, some bag contains all owners of candidates meeting $K$.
--
--   The result holds for every candidate family passing these geometric conditions, independently of stability or optimality. In the source algorithm, optional components satisfy the stronger diameter bound $\operatorname{diam}(K)<2b<2R$. Thus this establishes the geometric support-containment hypothesis used to allocate the actual point predicates, optional-component predicates, and optional-component count/cost contributions to bags. It assumes a tree decomposition as input; constructing that decomposition and compiling the DP are separate obligations.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Appendix A.6, paragraphs beginning "On every input, each constraint involves a clique" and "A tree decomposition is a tree of bags". The proof uses 3R owner-to-member bounds, 6R point-scope diameter, and 6R+diam(K)≤8R optional-scope diameter.

import Definitions.Def_StableMSR_Recovery_Geometry
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem clustering_constraint_bag_placement {n : ℕ} {I T : Type}
    [Fintype T] [DecidableEq T]
    (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (R : ℝ) (hR : 0 ≤ R)
    (N : Cluster n) (pool : Finset I) (candidate : I → Cluster n)
    (center : I → Point n) (owner : I → N)
    (howner : ∀ i ∈ pool, d (owner i) (center i) ≤ 2 * R)
    (hcandidate : ∀ i ∈ pool, ∀ x ∈ candidate i, d (center i) x ≤ R)
    (optional : Partition n) (hdiam : ∀ K ∈ optional, diameter d K ≤ 2 * R)
    (tree : SimpleGraph T) (bags : T → Finset N)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition
      ((thresholdGraph d (8 * R) N).induce (N : Set (Point n))) tree bags) :
    (∀ x : Point n, ∃ t : T, ∀ i ∈ pool, x ∈ candidate i → owner i ∈ bags t) ∧
      (∀ K ∈ optional, ∃ t : T, ∀ i ∈ pool,
        (candidate i ∩ K).Nonempty → owner i ∈ bags t) := by sorry

end StableMSR.Recovery
