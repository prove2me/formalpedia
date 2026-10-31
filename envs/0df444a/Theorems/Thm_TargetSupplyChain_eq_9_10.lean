-- Prove2me | Theorems.Thm_TargetSupplyChain_eq_9_10
-- name    : TargetSupplyChain.eq_9_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:03.034019+00:00
-- url     : https://prove2.me/theorems/e980f65f-564e-42e5-b346-941218e33e5b
-- title:
--   Risk-neutral decentralized solution (9)–(10) and footnote 6: $w^*_{nn}$, $y^*_{nn}$, $\pi^{s*}_{nn}$, $\pi^{r*}_{nn}$
-- statement:
--   Let $0<c<p$, $a\ge0$, $b>0$, demand $D\sim U[a,a+b]$, and $\xi^c=(p-c)/p$. In the "NN" game (risk-neutral supplier and retailer, the supplier leads):
--
--   1. If $b/a>1/\xi^c$, there is exactly one NN outcome, given by (9),
--   $$w^*_{nn}=\frac{p(a+b)+bc}{2b},\qquad y^*_{nn}=\frac{p(a+b)-bc}{2p},$$
--   and the supplier's and retailer's profits there are (10),
--   $$\pi^{s*}_{nn}=\frac{[p(a+b)-bc]^2}{4bp},\qquad \pi^{r*}_{nn}=\frac{[p(a+b)-bc]^2}{8bp}-\frac{pa^2}{2b}.$$
--   2. If $b/a\le1/\xi^c$ (footnote 6), there is exactly one NN outcome, $w^*_{nn}=p$, $y^*_{nn}=a$, with $\pi^{r*}_{nn}=0$ and $\pi^{s*}_{nn}=(p-c)a$.
--
--   Here an NN outcome is a limit of supplier-optimal pairs (wholesale price in $[c,p)$, the retailer's expected-profit-maximizing order), and the profits are $\pi^s=(w-c)y$ and $\pi^r=p\,\mathbb E[\min(D,y)]-wy$ at the outcome. This is the double-marginalization benchmark $\Pi^*_{nn}=\pi^{s*}_{nn}+\pi^{r*}_{nn}$ of Proposition 8.
--
--   Differences from the source:
--   - reading: standing parameters: c ≤ w ≤ p (p.10), a and b non-negative (p.11), D continuously distributed with a density (p.10), α a positive number (p.9) → 0 < c < p, 0 ≤ a, 0 < b (and 0 < αʳ where αʳ appears); reason: b > 0 because U[a, a+b] has a density; c < p makes ξᶜ > 0 (Prop. 2 divides by ξᶜ); c > 0 is used by the paper's proofs (they divide by c) and keeps bξᶜ + a < a + b
--   - reading: the supplier maximizes (w − c)y over c ≤ w ≤ p (4); the solution is written w* = p − ε, y* = αʳ − ε with ε "an infinitely small positive number" (p.12) → an outcome is a limit (w*, y*) of pairs (wₙ, yₙ) with wₙ ∈ [c, p), yₙ a best response to wₙ, and (wₙ − c)yₙ tending to the supremum of the supplier's profit; profits are evaluated at the limit pair; reason: at w = p every y ∈ [0, a] is a best response (p.13: the supplier "will avert from setting the wholesale price to be equal to the retail price"), and for αʳ > a the supremum over w < p is not attained; p − ε, αʳ − ε are the limits p, αʳ
--   - encoding: b/a > 1/ξᶜ and b/a ≤ 1/ξᶜ → a < bξᶜ and bξᶜ ≤ a; reason: no division by a; the same instances, including a = 0 (b/a = +∞)
--   - reading: "the optimal order quantity and wholesale price are given as follows" → an NN outcome exists and every NN outcome equals the stated pair (an iff); reason: "the optimal" decisions assert existence and uniqueness
--   - reading: footnote 6: "The supplier's and the retailer's profits are πʳ*_nn = 0 and πˢ*_nn = (p − c)a, respectively" → retailer's profit 0 and supplier's profit (p − c)a; reason: the words are in the opposite order to the symbols; the symbols are right (the retailer earns 0 at w = p, y = a)
--   - encoding: D uniformly distributed in [a, a+b]; E[min(y, D)] → the law (1/b)·Lebesgue restricted to [a, a+b]; E[min(y, D)] is the integral of min(d, y) against it; reason: Lean representation of the uniform law; the same instances
-- source:
--   Chen–Tang, Supply Chain Performance with Target-Oriented Firms, SSRN 3533746 (version of July 6, 2021), §4.1, eqs. (9)–(10), p.12, and footnote 6, p.12

import Mathlib
import Definitions.Def_TargetSupplyChain_Model

namespace TargetSupplyChain

/-- **The decentralized NN solution for uniform demand**, (9)–(10) and footnote 6,
Chen–Tang, *Supply Chain Performance with Target-Oriented Firms*, SSRN 3533746 (version of
July 6, 2021), §4.1, p.12.

For demand `D ~ U[a, a + b]`, risk-neutral supplier and retailer:

1. if `b/a > 1/ξᶜ`, the NN outcome is unique and equals
   `w*_nn = (p(a + b) + bc)/(2b)`, `y*_nn = (p(a + b) − bc)/(2p)` (9), with profits
   `πˢ*_nn = [p(a + b) − bc]²/(4bp)` and `πʳ*_nn = [p(a + b) − bc]²/(8bp) − pa²/(2b)` (10);
2. if `b/a ≤ 1/ξᶜ`, the NN outcome is unique and equals `w*_nn = p`, `y*_nn = a`, with
   `πʳ*_nn = 0` and `πˢ*_nn = (p − c)a` (footnote 6).

**Formalization Note** `b/a > 1/ξᶜ` is written `a < b ξᶜ` (no division by `a`; right for
`a = 0`, `b/a = +∞`). Outcomes are limits of supplier-optimal sequences over `w ∈ [c, p)`
(`nnOutcome`); in case 2 the supremum is not attained for `bξᶜ < a` and `(p, a)` is the limit
pair. The equivalences assert existence as well as uniqueness. -/
theorem eq_9_10 (P : Params) (hP : P.Standing) :
    (P.a < P.b * P.xi →
      (∀ w y : ℝ, nnOutcome P w y ↔
          w = (P.p * (P.a + P.b) + P.b * P.c) / (2 * P.b) ∧
            y = (P.p * (P.a + P.b) - P.b * P.c) / (2 * P.p)) ∧
        supplierProfit P ((P.p * (P.a + P.b) + P.b * P.c) / (2 * P.b))
            ((P.p * (P.a + P.b) - P.b * P.c) / (2 * P.p)) =
          (P.p * (P.a + P.b) - P.b * P.c) ^ 2 / (4 * P.b * P.p) ∧
        retailerProfit P ((P.p * (P.a + P.b) + P.b * P.c) / (2 * P.b))
            ((P.p * (P.a + P.b) - P.b * P.c) / (2 * P.p)) =
          (P.p * (P.a + P.b) - P.b * P.c) ^ 2 / (8 * P.b * P.p) - P.p * P.a ^ 2 / (2 * P.b)) ∧
    (P.b * P.xi ≤ P.a →
      (∀ w y : ℝ, nnOutcome P w y ↔ w = P.p ∧ y = P.a) ∧
        retailerProfit P P.p P.a = 0 ∧
        supplierProfit P P.p P.a = (P.p - P.c) * P.a) := by sorry

end TargetSupplyChain
