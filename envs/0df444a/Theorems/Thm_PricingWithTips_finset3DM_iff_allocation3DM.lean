-- Prove2me | Theorems.Thm_PricingWithTips_finset3DM_iff_allocation3DM
-- name    : PricingWithTips.finset3DM_iff_allocation3DM
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T20:16:06.218442+00:00
-- url     : https://prove2.me/theorems/204462fd-26eb-4e47-a256-311e8d7bb842
-- title:
--   Exact-cover and allocation formulations of 3DM are equivalent
-- statement:
--   Let the three vertex classes each be indexed by $\operatorname{Fin}(n)$, and let $T$ be a finite set of admissible triples. Then $T$ contains a perfect three-dimensional matching in the exact-cover sense if and only if there is a full allocation in which every buyer, store, and courier is used at most once and every allocated triple belongs to $T$.
--
--   This equivalence connects the conventional finite-set formulation of 3DM to the allocation predicate used in the reductions for Theorems 4.1 and 4.2.
-- source:
--   Chen, Hu, Li, and Wang, Online Food Delivery Platforms: Pricing with Tips, arXiv:2507.10872v1, Section 4, reduction from 3-dimensional matching, https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips_Finset3DM

namespace PricingWithTips

theorem finset3DM_iff_allocation3DM (n : ℕ)
    (T : Finset (ThreeDMTriple n)) :
    HasPerfectFinset3DM n T ↔
      HasPerfect3DMatching n (fun b s d => decide ((b, s, d) ∈ T)) := by sorry

end PricingWithTips
