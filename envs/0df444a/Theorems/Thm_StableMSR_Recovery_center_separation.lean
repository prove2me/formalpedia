-- Prove2me | Theorems.Thm_StableMSR_Recovery_center_separation
-- name    : StableMSR.Recovery.center_separation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:30.290887+00:00
-- url     : https://prove2.me/theorems/d57e5d11-2ab0-4181-9935-0cf7ccdcb0af
-- title:
--   Lemma 3.3 — center and cluster separation
-- statement:
--   Let $\mathcal O$ be the unique optimum of a $\gamma$-stable finite real metric instance, $\gamma>1$, and put $\varepsilon=\gamma-1$. For any $C\in\mathcal O$ and any optimal in-cluster center $c$,
--   $$
--   \forall p\notin C,\quad d(c,p)>\gamma r(C),
--   $$
--   $$
--   \operatorname{dist}(C,P\setminus C)>\varepsilon r(C),\qquad
--   C=B(c,r(C))=B(c,\gamma r(C)).
--   $$
--   These are separation and closed-ball identities for every optimal center, without a uniqueness assumption on centers. Empty complements have distance $+\infty$. The result supplies actual large-cluster candidate representations.
--
--   Differences from the source:
--   - encoding: An arbitrary finite real metric space with fixed input order and unordered clusters → Points are Fin n; clusters and unordered partitions are finite sets; metric arrays are Mathlib metric distances; reason: Relabelling preserves every finite ordered instance, all distance values, and every unordered partition
--   - encoding: The assertion is introduced with an outside point p and followed by two consequences → For each cluster and optimal center the outside-point inequality is universally quantified, with both consequences in the same conjunction; reason: The consequences also apply when the complement is empty; its distance is +infinity
--   - encoding: Set distance is a minimum, with value +infinity if either set is empty → Set distance is the EReal infimum of the finite set of pairwise real distances; finite bounds and radii are coerced to EReal; reason: The complete-lattice empty infimum is +infinity, and a nonempty finite infimum is the same attained minimum; all added radii are finite
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma 3.3, p. 5; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem center_separation {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ)
    (O : Partition n) (hO : Stable d k γ O)
    (C : Cluster n) (hC : C ∈ O) (c : Point n) (hc : OptimalCenter d C c) :
    (∀ p : Point n, p ∉ C → γ * radius d C < d c p) ∧
    ((γ - 1) * radius d C : EReal) < setDistance d C (Finset.univ \ C) ∧
    C = ball d c (radius d C) ∧ C = ball d c (γ * radius d C) := by sorry

end StableMSR.Recovery
