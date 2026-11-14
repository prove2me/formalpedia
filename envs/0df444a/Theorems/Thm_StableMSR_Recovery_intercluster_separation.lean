-- Prove2me | Theorems.Thm_StableMSR_Recovery_intercluster_separation
-- name    : StableMSR.Recovery.intercluster_separation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:38.221079+00:00
-- url     : https://prove2.me/theorems/9541b639-51bb-4358-a92c-8740ad5e3999
-- title:
--   Corollary 3.7 — intercluster separation
-- statement:
--   Let $\mathcal O$ be the optimum of a $\gamma$-stable instance, $\varepsilon=\gamma-1>0$. For any three pairwise distinct optimal clusters $C,D,E$, with $C$ nonsingleton,
--   $$
--   \operatorname{dist}(D,E)+\min\{r(D),r(E)\}>\varepsilon r(C).
--   $$
--   Only $C$ must be nonsingleton. This provides the separation needed to recognize small clusters as global threshold-graph components.
--
--   Differences from the source:
--   - encoding: An arbitrary finite real metric space with fixed input order and unordered clusters → Points are Fin n; clusters and unordered partitions are finite sets; metric arrays are Mathlib metric distances; reason: Relabelling preserves every finite ordered instance, all distance values, and every unordered partition
--   - encoding: Set distance is a minimum, with value +infinity if either set is empty → Set distance is the EReal infimum of the finite set of pairwise real distances; finite bounds and radii are coerced to EReal; reason: The complete-lattice empty infimum is +infinity, and a nonempty finite infimum is the same attained minimum; all added radii are finite
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Corollary 3.7, p. 6; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem intercluster_separation {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ)
    (O : Partition n) (hO : Stable d k γ O)
    (C D E : Cluster n) (hC : C ∈ O) (hD : D ∈ O) (hE : E ∈ O)
    (hCD : C ≠ D) (hCE : C ≠ E) (hDE : D ≠ E) (hns : 2 ≤ C.card) :
    ((γ - 1) * radius d C : EReal) <
      setDistance d D E + (min (radius d D) (radius d E) : EReal) := by sorry

end StableMSR.Recovery
