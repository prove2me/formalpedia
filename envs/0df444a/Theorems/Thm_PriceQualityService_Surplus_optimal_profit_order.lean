-- Prove2me | Theorems.Thm_PriceQualityService_Surplus_optimal_profit_order
-- name    : PriceQualityService.Surplus.optimal_profit_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:18:54.732767+00:00
-- url     : https://prove2.me/theorems/b1057b6b-bae6-41fa-b858-23d7c00e35c6
-- title:
--   $r^\dagger\le r^\ddagger\le r^*$: more decisions, more profit
-- statement:
--   Assume $c_i>0$ for all $i$ and $t_s\le t_l$. Fix pre-determined qualities $\mathbf q\in\mathbb R^N$ and durations $\mathbf t\in[t_s,t_l]^N$. Let $\mathbf p^\dagger$ be an optimal solution of the price-only problem at $(\mathbf q,\mathbf t)$, $(\mathbf p^\ddagger,\mathbf t^\ddagger)$ an optimal solution of the price-and-service problem at the same $\mathbf q$, and $(\mathbf p^*,\mathbf q^*,\mathbf t^*)$ an optimal solution of the joint problem (4). Then
--   $$
--   \Pi(\mathbf p^\dagger,\mathbf q,\mathbf t;\mathcal N)\le\Pi(\mathbf p^\ddagger,\mathbf q,\mathbf t^\ddagger;\mathcal N)\le\Pi(\mathbf p^*,\mathbf q^*,\mathbf t^*;\mathcal N),
--   $$
--   that is, $r^\dagger\le r^\ddagger\le r^*$.
--
--   Each problem's feasible set contains the previous one's, so the firm earns at least as much when it controls more decisions; in the proof of Proposition 5 this ordering of profits becomes the ordering of consumer surplus.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 2 (PDF p. 35), proof of Proposition 5

import Mathlib
import Definitions.Def_PriceQualityService_Surplus_Problems

namespace PriceQualityService.Surplus

open Finset

/-- `r† ⩽ r‡ ⩽ r*`, Wang, Ke & Cui, accepted manuscript (SSRN 3766191), Online Supplement p. 2,
proof of Proposition 5. Fix qualities `q` and durations `t ∈ [t_s, t_l]^N`. Let `p†` maximize
the price-only problem at `(q, t)`, `(p‡, t‡)` the price-and-service problem at the same `q`, and
`(p*, q*, t*)` the joint problem (4). Then the optimal profits are ordered:
`Π(p†, q, t) ⩽ Π(p‡, q, t‡) ⩽ Π(p*, q*, t*)`. -/
theorem optimal_profit_order {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ)
    (hc : ∀ i, 0 < c i) (hts : ts ≤ tl)
    (q t : Fin N → ℝ) (ht : ∀ i, t i ∈ Set.Icc ts tl)
    (pDag : Fin N → ℝ) (hDag : IsPriceOptimal α a b c s q t pDag)
    (pDdag tDdag : Fin N → ℝ) (hDdag : IsPriceServiceOptimal α a b c s ts tl q pDdag tDdag)
    (pStar qStar tStar : Fin N → ℝ) (hStar : IsJointOptimal α a b c s ts tl pStar qStar tStar) :
    PriceQualityService.Joint.profit α a b c s pDag q t ≤ PriceQualityService.Joint.profit α a b c s pDdag q tDdag ∧
      PriceQualityService.Joint.profit α a b c s pDdag q tDdag ≤ PriceQualityService.Joint.profit α a b c s pStar qStar tStar := by sorry

end PriceQualityService.Surplus
