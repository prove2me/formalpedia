-- Prove2me | Theorems.Thm_TargetSupplyChain_centralized_uniform
-- name    : TargetSupplyChain.centralized_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:13.31104+00:00
-- url     : https://prove2.me/theorems/b1fb1bb7-4fd9-4569-a7cb-66dc73f2c957
-- title:
--   Centralized newsvendor with uniform demand: $y^{c*}_{nn}=(p(a+b)-bc)/p$ and $\Pi^{c*}_{nn}$ (§4.1, p.11)
-- statement:
--   Let $0<c<p$, $a\ge0$, $b>0$, and let the demand $D$ be uniformly distributed on $[a,a+b]$. Consider the centralized supply chain's problem (8),
--   $$\max_{y\ge0}\ \Pi^c_{nn}(y)=p\,\mathbb E[\min(y,D)]-cy.$$
--   Its maximum value is
--   $$\Pi^{c*}_{nn}=\frac{[p(a+b)-bc]^2}{2bp}-\frac{pa^2}{2b},$$
--   and, among $y\ge0$, it is attained exactly at
--   $$y^{c*}_{nn}=\frac{p(a+b)-bc}{p}=b\xi^c+a .$$
--
--   This is the first-best benchmark against which the decentralized supply chains of the mission are compared; Proposition 8(3) says that a target-oriented retailer with $\alpha^r=b\xi^c+a$ attains it.
--
--   Differences from the source:
--   - reading: standing parameters: c ≤ w ≤ p (p.10), a and b non-negative (p.11), D continuously distributed with a density (p.10), α a positive number (p.9) → 0 < c < p, 0 ≤ a, 0 < b (and 0 < αʳ where αʳ appears); reason: b > 0 because U[a, a+b] has a density; c < p makes ξᶜ > 0 (Prop. 2 divides by ξᶜ); c > 0 is used by the paper's proofs (they divide by c) and keeps bξᶜ + a < a + b
--   - encoding: "the optimal order quantity yᶜ*_nn and the maximum supply chain profit Πᶜ*_nn are given by" → Πᶜ*_nn is the greatest element of Πᶜ_nn([0, ∞)), and for y ≥ 0, Πᶜ_nn(y) = Πᶜ*_nn iff y = yᶜ*_nn; reason: Lean form of "the maximizer and the maximum"; "the" optimal order quantity asserts uniqueness
--   - encoding: D uniformly distributed in [a, a+b]; E[min(y, D)] → the law (1/b)·Lebesgue restricted to [a, a+b]; E[min(y, D)] is the integral of min(d, y) against it; reason: Lean representation of the uniform law; the same instances
-- source:
--   Chen–Tang, Supply Chain Performance with Target-Oriented Firms, SSRN 3533746 (version of July 6, 2021), §4.1, display after (8), p.11

import Mathlib
import Definitions.Def_TargetSupplyChain_Model

namespace TargetSupplyChain

/-- **Centralized solution for uniform demand**, Chen–Tang, *Supply Chain Performance with
Target-Oriented Firms*, SSRN 3533746 (version of July 6, 2021), §4.1, display after (8), p.11.

For demand `D ~ U[a, a + b]`, the centralized problem (8),
`max_{y ≥ 0} Πᶜ_nn(y) = p E[min(y, D)] − c y`, has the maximum value
`Πᶜ*_nn = [p(a + b) − bc]²/(2bp) − pa²/(2b)`, attained exactly at
`yᶜ*_nn = (p(a + b) − bc)/p`.

**Formalization Note** Standing assumptions `0 < c < p`, `0 ≤ a`, `0 < b` (the printed
"non-negative" `b = 0` has no density). The maximum is stated as `IsGreatest` of the image of
`[0, ∞)`, and the maximizer as an equivalence over `y ≥ 0`. -/
theorem centralized_uniform (P : Params) (hP : P.Standing) :
    IsGreatest (centralProfit P '' Set.Ici 0)
        ((P.p * (P.a + P.b) - P.b * P.c) ^ 2 / (2 * P.b * P.p) - P.p * P.a ^ 2 / (2 * P.b)) ∧
      ∀ y : ℝ, 0 ≤ y →
        (centralProfit P y =
            (P.p * (P.a + P.b) - P.b * P.c) ^ 2 / (2 * P.b * P.p) - P.p * P.a ^ 2 / (2 * P.b) ↔
          y = (P.p * (P.a + P.b) - P.b * P.c) / P.p) := by sorry

end TargetSupplyChain
