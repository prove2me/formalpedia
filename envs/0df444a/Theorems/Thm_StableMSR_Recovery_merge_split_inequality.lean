-- Prove2me | Theorems.Thm_StableMSR_Recovery_merge_split_inequality
-- name    : StableMSR.Recovery.merge_split_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:37.942516+00:00
-- url     : https://prove2.me/theorems/7cda8bbb-0e37-4210-a007-25db230c03be
-- title:
--   Lemma 3.6 — merge-and-split inequality
-- statement:
--   Let $\mathcal O$ be the optimum of a $\gamma$-stable instance, with $\varepsilon=\gamma-1>0$. Let $D_1,\ldots,D_s$ be distinct optimal clusters, $s\ge2$, and let $C_1,\ldots,C_{s-1}$ be distinct nonsingleton optimal clusters outside that family. Then
--   $$
--   r\!\left(\bigcup_{j=1}^sD_j\right)>\sum_{j=1}^sr(D_j)+\varepsilon\sum_{i=1}^{s-1}r(C_i).
--   $$
--   The inequality is strict and has no locality assumption on the cluster families. It links local merging costs to splitting savings elsewhere in the instance.
--
--   Differences from the source:
--   - encoding: An arbitrary finite real metric space with fixed input order and unordered clusters → Points are Fin n; clusters and unordered partitions are finite sets; metric arrays are Mathlib metric distances; reason: Relabelling preserves every finite ordered instance, all distance values, and every unordered partition
--   - encoding: Distinct indexed cluster families → Finite sets of clusters with disjointness and exact cardinality relations; reason: Only distinct clusters are used, and the inequalities and union are invariant under reindexing
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma 3.6, p. 6; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem merge_split_inequality {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ)
    (O : Partition n) (hO : Stable d k γ O)
    (D F : Partition n) (hD : D ⊆ O) (hF : F ⊆ O)
    (hdisj : Disjoint D F) (hsize : 2 ≤ D.card) (hcount : F.card + 1 = D.card)
    (hnonsingleton : ∀ C ∈ F, 2 ≤ C.card) :
    cost d D + (γ - 1) * cost d F < radius d (D.biUnion id) := by sorry

end StableMSR.Recovery
