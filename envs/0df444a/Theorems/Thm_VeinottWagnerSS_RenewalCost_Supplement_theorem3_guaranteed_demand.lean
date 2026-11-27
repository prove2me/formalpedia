-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_Supplement_theorem3_guaranteed_demand
-- name    : VeinottWagnerSS.RenewalCost.Supplement.theorem3_guaranteed_demand
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:26:58.990913+00:00
-- url     : https://prove2.me/theorems/9e18b7e2-6ca4-428e-995f-fd2e8099066d
-- title:
--   Theorem 3 — if $\varphi(k)=0$ for $k=0,1,\dots,\bar S-\underline s$, then $(\underline s,\underline S)$ is optimal for the finite and infinite period models
-- statement:
--   Consider the periodic-review inventory model of Veinott and Wagner with i.i.d. integer demands of distribution $\varphi$ with finite mean, set-up cost $K\ge0$, discount factor $0\le\alpha\le1$, and expected one-period cost $G_\alpha:\mathbb Z\to\mathbb R$ that is convex and satisfies $G_\alpha(y)\to+\infty$ as $|y|\to\infty$. Let $\underline S$ be the smallest minimizer of $G_\alpha$, $\bar S$ the smallest integer $\bar S\ge\underline S$ with $G_\alpha(\bar S+1)\ge G_\alpha(\underline S)+\alpha K$ (Eq. (21)), and $\underline s$ the smallest integer with $G_\alpha(\underline s)\le G_\alpha(\underline S)+K$ (Eq. (22)).
--
--   Suppose the demand in each period exceeds $\bar S-\underline s$ with certainty:
--
--   $$
--   \varphi(k)=0,\qquad k=0,1,\dots,\bar S-\underline s .
--   $$
--
--   Then the stationary policy $(\underline s,\underline S)$ — order up to $\underline S$ whenever the stock on hand plus on order is below $\underline s$, otherwise do not order — is optimal for every initial level $X_1$:
--
--   1. for the $n$-period model with cost $f_n(x\mid Y)$ of Eq. (2), for every $n=1,2,\dots$;
--   2. for the infinite period model: with the discounted cost $f(x\mid Y)$ of Eq. (3) when $0\le\alpha<1$, and with the average cost $a_1(x\mid Y)=\liminf_n f_n(x\mid Y)/n$ of Eq. (4) when $\alpha=1$.
--
--   Optimality is against every admissible policy, which may depend on the whole past history.
--
--   Under this demand assumption an optimal policy is found at the cost of a one-period computation; once an order is placed, an order is placed in every later period.
--
--   **Formalization Note** The model is the reduced one of Eq. (2), p. 529: the unit purchase cost is absorbed into $G_\alpha$, which is a primitive `G : ℤ → ℝ`; convexity is monotone forward differences and coercivity is `Tendsto G atTop atTop` and `Tendsto G atBot atTop`. Demand is a `PMF ℕ` with finite mean $\sum_k k\varphi(k)<\infty$ (p. 528). $\underline S,\bar S,\underline s$ are the published `SLow G`, `SHigh G K α`, `sLow G K`. The policy is `stationary (sLow G K) (SLow G)`; finite-horizon optimality is `IsOptimal` for every `n ≥ 1` and infinite-horizon optimality is `IsInfOptimal`. The standing assumption $\alpha\varphi(0)<1$ of §3 is not a separate hypothesis because the demand hypothesis gives $\varphi(0)=0$ (as $\bar S\ge\underline S\ge\underline s$).
--
--   Differences from the source:
--   - encoding: the model with unit cost c and holding and penalty cost L → the reduced model with a convex, two-sided coercive G_α : ℤ → ℝ as primitive; reason: Eq. (2), p. 529, shows the optimization depends on the model only through G_α, and every convex coercive G is G_α for c = 0, L = G.
--   - encoding: f(x | Y) = lim f_n(x | Y) of (3) → liminf of f_n(x | Y); reason: under the theorem's hypotheses (α < 1, K ≥ 0, G bounded below) the limit exists in [−∞, +∞] and equals the liminf; the liminf form is total.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 545, Theorem 3; proof in the Appendix, §4, pp. 551–552; critical numbers (21)–(22), p. 537; criteria (2)–(4), pp. 529–530

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers
import Definitions.Def_VeinottWagnerSS_RenewalCost_Supplement_InfiniteHorizon

open scoped ENNReal

namespace VeinottWagnerSS.RenewalCost.Supplement

open VeinottWagnerSS.Bounds

/-- Theorem 3, p. 545 (proof: Appendix §4, pp. 551–552). If `φ(k) = 0` for
`k = 0, 1, ⋯, S̄ − s̲`, then the stationary policy `(s̲, S̲)` is optimal, for every initial level
`X₁`, for every finite-period model and for the infinite-period model (discounted for
`0 ≤ α < 1`, average cost for `α = 1`). Here `S̲ = SLow G`, `s̲ = sLow G K` and
`S̄ = SHigh G K α` are the numbers of (21)–(22), p. 537. -/
theorem theorem3_guaranteed_demand (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (hgap : ∀ k : ℕ, (k : ℤ) ≤ SHigh G K α - sLow G K → φ k = 0) :
    (∀ n : ℕ, 1 ≤ n → IsOptimal φ G K α n (stationary (sLow G K) (SLow G))) ∧
      IsInfOptimal φ G K α (stationary (sLow G K) (SLow G)) := by sorry

end VeinottWagnerSS.RenewalCost.Supplement
