-- Prove2me | Theorems.Thm_RetailVariety_Statics_lhs13_increasing_in_lam
-- name    : RetailVariety.Statics.lhs13_increasing_in_lam
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:52.665814+00:00
-- url     : https://prove2.me/theorems/d870a448-096e-40c3-8731-22e6996c07fd
-- title:
--   The left side of (13) is increasing and unbounded in the store volume $\lambda$
-- statement:
--   Fix $0<c<p$, $\sigma>0$ and $0\le\beta<1$, and let $z=\Phi^{-1}(1-c/p)$. The left side of (13),
--   $$L(\lambda)=\left(1-\frac{c}{p}\right)\frac{\sqrt{2\pi}}{\sigma}\lambda^{1-\beta}e^{z^2/2},$$
--   is strictly increasing in $\lambda\in(0,\infty)$, and $L(\lambda)\to\infty$ as $\lambda\to\infty$.
--
--   The right side of (13) does not involve $\lambda$, so this is the volume effect of part (c) of Theorem 2 in the independent model.
--
--   **Formalization Note** The paper states only that the left side is increasing in $\lambda$; unboundedness (immediate from $\beta<1$) is added as a second conjunct because part (c) needs it.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1508, Appendix, Proof of Theorem 2, part (c)

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology

namespace RetailVariety.Statics

theorem lhs13_increasing_in_lam (p c σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hσ : 0 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    StrictMonoOn (fun lam : ℝ => (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
        * Real.exp (criticalFractile p c ^ 2 / 2)) (Set.Ioi 0) ∧
      Tendsto (fun lam : ℝ => (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
        * Real.exp (criticalFractile p c ^ 2 / 2)) atTop atTop := by sorry

end RetailVariety.Statics
