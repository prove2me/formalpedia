-- Prove2me | Theorems.Thm_TargetSupplyChain_proposition_2
-- name    : TargetSupplyChain.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:40.859992+00:00
-- url     : https://prove2.me/theorems/769d4c18-8fef-4d23-b6b8-90b1be6f721f
-- title:
--   Proposition 2: the NT decisions $(w^*_{nt},y^*_{nt})$ in the three target regimes (corrected: $\alpha^r<a+b$)
-- statement:
--   Let $0<c<p$, $a\ge0$, $b>0$, demand $D\sim U[a,a+b]$, $\xi^c=(p-c)/p$, and let the target coefficient satisfy $0<\alpha^r$, $a\le\alpha^r<a+b$. In the "NT" game (risk-neutral supplier, target-oriented retailer with target $\tau^r=\alpha^r(p-w)$), an NT outcome exists, and every NT outcome $(w^*_{nt},y^*_{nt})$ is as follows.
--
--   1. If $b/a\le2/\xi^c$: $(w^*_{nt},y^*_{nt})=(p,\alpha^r)$.
--   2. If $b/a>2/\xi^c$:
--   $$
--   (w^*_{nt},y^*_{nt})=\begin{cases}\Big(\dfrac{p(2a+b-2\alpha^r)}{b},\ 2\alpha^r-a\Big), & \alpha^r\in[a,\alpha^{r1}_{nt}),\\[2mm] (w^1_{nt},\ y^1_{nt}), & \alpha^r\in[\alpha^{r1}_{nt},\alpha^{r2}_{nt}),\\[1mm] (p,\ \alpha^r), & \alpha^r\in[\alpha^{r2}_{nt},a+b),\end{cases}
--   $$
--   with $\alpha^{r1}_{nt},\alpha^{r2}_{nt},w^1_{nt},y^1_{nt}$ the closed forms of p.12.
--
--   The pair $(p,\alpha^r)$ is the paper's $(p-\epsilon,\alpha^r-\epsilon)$: the supplier's supremum is approached as $w\uparrow p$ and not attained. An NT outcome is a limit of supplier-optimal pairs (wholesale price in $[c,p)$, the target-oriented retailer's CSM-maximizing order).
--
--   Differences from the source:
--   - correction: αʳ ∈ [a, a + b] (Prop. 2) and αʳ ∈ [ᾱʳ¹_I, a + b] (Prop. 8) → αʳ < a + b; reason: at αʳ = a + b the target (a+b)(p − w) exceeds V(y; D) almost surely for every order y and every w < p, so every order has CSM −1, every y ≥ 0 is a best response and the supplier's profit is unbounded: the NT decisions are undefined. Counterexample: (p, c, a, b, αʳ) = (10, 4, 1, 99, 100)
--   - reading: the supplier maximizes (w − c)y over c ≤ w ≤ p (4); the solution is written w* = p − ε, y* = αʳ − ε with ε "an infinitely small positive number" (p.12) → an outcome is a limit (w*, y*) of pairs (wₙ, yₙ) with wₙ ∈ [c, p), yₙ a best response to wₙ, and (wₙ − c)yₙ tending to the supremum of the supplier's profit; profits are evaluated at the limit pair; reason: at w = p every y ∈ [0, a] is a best response (p.13: the supplier "will avert from setting the wholesale price to be equal to the retail price"), and for αʳ > a the supremum over w < p is not attained; p − ε, αʳ − ε are the limits p, αʳ
--   - encoding: b/a ≤ 2/ξᶜ and b/a > 2/ξᶜ → bξᶜ ≤ 2a and 2a < bξᶜ; reason: no division by a; the same instances, including a = 0 (b/a = +∞)
--   - reading: standing parameters: c ≤ w ≤ p (p.10), a and b non-negative (p.11), D continuously distributed with a density (p.10), α a positive number (p.9) → 0 < c < p, 0 ≤ a, 0 < b (and 0 < αʳ where αʳ appears); reason: b > 0 because U[a, a+b] has a density; c < p makes ξᶜ > 0 (Prop. 2 divides by ξᶜ); c > 0 is used by the paper's proofs (they divide by c) and keeps bξᶜ + a < a + b
--   - reading: CVaR_η(V) = E[V | V ≤ q_{1−η}(V)] for η ∈ [0,1) and E[V | V ≥ q_{−η}(V)] for η ∈ (−1,0), with q_η the unique η-quantile (Definition 1, p.6) → CVaR_η = average of the quantile function over (0, 1−η] (η ≥ 0), resp. over (−η, 1] (η < 0); reason: V(y; D) has an atom at (p − w)y, so the unique quantile does not exist; the quantile average equals the printed formula whenever it does, and is the form the Online Appendix computes with
--   - reading: "the supplier's optimal wholesale price … and the retailer's optimal order quantity … are given as follows" → an NT outcome exists and every NT outcome equals the stated pair; reason: "the optimal" decisions assert existence and uniqueness
--   - encoding: D uniformly distributed in [a, a+b]; E[min(y, D)] → the law (1/b)·Lebesgue restricted to [a, a+b]; E[min(y, D)] is the integral of min(d, y) against it; reason: Lean representation of the uniform law; the same instances
-- source:
--   Chen–Tang, Supply Chain Performance with Target-Oriented Firms, SSRN 3533746 (version of July 6, 2021), §4.2, Proposition 2, p.13 (closed forms p.12)

import Mathlib
import Definitions.Def_TargetSupplyChain_Model
import Definitions.Def_TargetSupplyChain_ClosedForms

namespace TargetSupplyChain

/-- **Proposition 2** (corrected: `αʳ < a + b`), Chen–Tang, *Supply Chain Performance with
Target-Oriented Firms*, SSRN 3533746 (version of July 6, 2021), §4.2, p.13.

For demand `D ~ U[a, a + b]` and every target coefficient `αʳ` with `0 < αʳ`,
`a ≤ αʳ < a + b`, an NT outcome exists, and every NT outcome `(w*_nt, y*_nt)` is:

1. if `b/a ≤ 2/ξᶜ`: `(p, αʳ)`;
2. if `b/a > 2/ξᶜ`:
   * `(p(2a + b − 2αʳ)/b, 2αʳ − a)` for `αʳ ∈ [a, αʳ¹_nt)`;
   * `(w¹_nt, y¹_nt)` for `αʳ ∈ [αʳ¹_nt, αʳ²_nt)`;
   * `(p, αʳ)` for `αʳ ∈ [αʳ²_nt, a + b)`.

**Formalization Note** The printed `w* = p − ε`, `y* = αʳ − ε` ("ε an infinitely small positive
number", p.12) are the limit pair `(p, αʳ)` of supplier-optimal sequences over `w ∈ [c, p)`
(`ntOutcome`). `b/a ≤ 2/ξᶜ` is written `bξᶜ ≤ 2a` (no division by `a`). The printed ranges
`[a, a + b]` and `[αʳ²_nt, a + b]` are corrected to exclude `αʳ = a + b`, where the outcome is
undefined. The closed forms `αʳ¹_nt`, `αʳ²_nt`, `w¹_nt`, `y¹_nt` are transcribed from p.12. -/
theorem proposition_2 (P : Params) (hP : P.Standing) (α : ℝ) (hα : P.InDom α) :
    (∃ w y : ℝ, ntOutcome P α w y) ∧
      ∀ w y : ℝ, ntOutcome P α w y →
        (P.b * P.xi ≤ 2 * P.a → w = P.p ∧ y = α) ∧
        (2 * P.a < P.b * P.xi →
          (α < alphaR1 P →
              w = P.p * (2 * P.a + P.b - 2 * α) / P.b ∧ y = 2 * α - P.a) ∧
            (alphaR1 P ≤ α → α < alphaR2 P → w = w1nt P α ∧ y = y1nt P α) ∧
            (alphaR2 P ≤ α → w = P.p ∧ y = α)) := by sorry

end TargetSupplyChain
