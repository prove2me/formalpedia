-- Prove2me | Theorems.Thm_RetailVariety_Statics_lhs13_increasing_in_p
-- name    : RetailVariety.Statics.lhs13_increasing_in_p
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:38.549541+00:00
-- url     : https://prove2.me/theorems/52d6d08e-5691-4b32-b3b5-daf670620e1c
-- title:
--   $z$ and the left side of (13) are increasing in the price $p$
-- statement:
--   Fix a unit cost $c>0$, store volume $\lambda>0$, $\sigma>0$ and $0\le\beta<1$. On the price range $p\in(c,\infty)$:
--
--   1. the critical fractile $z(p)=\Phi^{-1}(1-c/p)$ is strictly increasing in $p$;
--   2. the left side of (13),
--   $$L(p)=\left(1-\frac{c}{p}\right)\frac{\sqrt{2\pi}}{\sigma}\lambda^{1-\beta}e^{z(p)^2/2},$$
--   is strictly increasing in $p$.
--
--   The right side of (13) does not involve $p$, so this monotonicity is the price effect behind part (a) of Theorem 2.
--
--   **Formalization Note** The paper says "increasing"; the strict form is stated, which is true and stronger. Note that $e^{z^2/2}$ alone is not monotone in $p$ (it decreases while $z<0$, i.e. for $p<2c$); the claim concerns the product.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1508, Appendix, Proof of Theorem 2, part (a)

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology

namespace RetailVariety.Statics

theorem lhs13_increasing_in_p (c lam σ β : ℝ) (hc : 0 < c) (hlam : 0 < lam) (hσ : 0 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    StrictMonoOn (fun p : ℝ => criticalFractile p c) (Set.Ioi c) ∧
      StrictMonoOn (fun p : ℝ => (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
          * Real.exp (criticalFractile p c ^ 2 / 2)) (Set.Ioi c) := by sorry

end RetailVariety.Statics
