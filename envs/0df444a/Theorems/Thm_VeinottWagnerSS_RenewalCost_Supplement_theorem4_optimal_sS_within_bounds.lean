-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_Supplement_theorem4_optimal_sS_within_bounds
-- name    : VeinottWagnerSS.RenewalCost.Supplement.theorem4_optimal_sS_within_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:27:25.408987+00:00
-- url     : https://prove2.me/theorems/fff827f9-bcb2-476e-9764-ecfb215fd313
-- title:
--   Theorem 4 — optimal $(s,S)$ policies with $\underline s\le s\le\bar s\le\underline S\le S\le\bar S$ for the $n$-period (a) and the infinite period (b) models
-- statement:
--   Consider the periodic-review inventory model of Veinott and Wagner with i.i.d. integer demands of distribution $\varphi$ with finite mean, set-up cost $K\ge0$, discount factor $0\le\alpha\le1$ with $\alpha\varphi(0)<1$, and expected one-period cost $G_\alpha:\mathbb Z\to\mathbb R$ that is convex and satisfies $G_\alpha(y)\to+\infty$ as $|y|\to\infty$. Define the four critical numbers of p. 537:
--
--   1. $\underline S$, the smallest integer minimizing $G_\alpha$;
--   2. $\bar S$, the smallest integer $\bar S\ge\underline S$ with $G_\alpha(\bar S+1)\ge G_\alpha(\underline S)+\alpha K$ (21);
--   3. $\underline s$, the smallest integer with $G_\alpha(\underline s)\le G_\alpha(\underline S)+K$ (22);
--   4. $\bar s$, the smallest integer with $G_\alpha(\bar s)\le G_\alpha(\underline S)+(1-\alpha)K$ (23).
--
--   Then:
--
--   **(a)** For every $n\ge2$ there is an optimal policy for the $n$-period model (cost $f_n(x\mid Y)$ of Eq. (2)) that is an $(s,S)$ policy and whose first-period rule $(s_n,S_n)$ satisfies
--
--   $$
--   \underline s\le s_n\le\bar s\le\underline S\le S_n\le\bar S .
--   $$
--
--   **(b)** For the infinite period model there is an optimal stationary $(s^*,S^*)$ policy with
--
--   $$
--   \underline s\le s^*\le\bar s\le\underline S\le S^*\le\bar S ;
--   $$
--
--   optimality is with respect to the discounted cost $f(x\mid Y)=\lim_n f_n(x\mid Y)$ of Eq. (3) when $0\le\alpha<1$, and with respect to the average cost $a_1(x\mid Y)=\liminf_n f_n(x\mid Y)/n$ of Eq. (4) when $\alpha=1$.
--
--   In both parts optimality is against every admissible, possibly history-dependent policy, and for every initial level of stock on hand plus on order.
--
--   The theorem reduces the search for an optimal policy to the finite box of pairs $(s,S)$ determined by one-period quantities; it underlies the paper's computational algorithm and the proof of Theorem 3.
--
--   **Formalization Note** The model is the reduced one of Eq. (2), p. 529, with $G_\alpha$ a primitive `G : ℤ → ℝ`, convexity as monotone forward differences and two-sided coercivity. Demand is a `PMF ℕ` with finite mean (p. 528), and $\alpha\varphi(0)<1$ is the standing assumption imposed on p. 533 and used thereafter. The critical numbers are the published `SLow G`, `SHigh G K α`, `sLow G K`, `sHigh G K α`. Part (a) restates the published `VeinottWagnerSS.Bounds.theorem4a_optimal_sS_within_bounds` in the same terms; part (b) uses `stationary sStar SStar` and `IsInfOptimal`.
--
--   Differences from the source:
--   - encoding: the model with unit cost c and holding and penalty cost L → the reduced model with a convex, two-sided coercive G_α : ℤ → ℝ as primitive; reason: Eq. (2), p. 529, shows the optimization depends on the model only through G_α, and every convex coercive G is G_α for c = 0, L = G.
--   - encoding: f(x | Y) = lim f_n(x | Y) of (3) → liminf of f_n(x | Y); reason: under the theorem's hypotheses (α < 1, K ≥ 0, G bounded below) the limit exists in [−∞, +∞] and equals the liminf; the liminf form is total.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 549, Theorem 4 (a) and (b); proof in the Appendix, §2, p. 550; critical numbers (21)–(23), p. 537; criteria (2)–(4), pp. 529–530; αφ(0) < 1, p. 533

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers
import Definitions.Def_VeinottWagnerSS_RenewalCost_Supplement_InfiniteHorizon

open scoped ENNReal

namespace VeinottWagnerSS.RenewalCost.Supplement

open VeinottWagnerSS.Bounds

/-- Theorem 4, p. 549 (proof: Appendix §2, p. 550), both parts.
(a) For the `n`-period model (`n = 2, 3, ⋯`) there exists an optimal `(s, S)` policy whose
first-period rule `(s_n, S_n)` satisfies `s̲ ≤ s_n ≤ s̄ ≤ S̲ ≤ S_n ≤ S̄`.
(b) For the infinite period model (discounted for `0 ≤ α < 1`, average cost for `α = 1`) there
exists an optimal stationary policy `(s*, S*)` with `s̲ ≤ s* ≤ s̄ ≤ S̲ ≤ S* ≤ S̄`.
Optimality is against every admissible (history-dependent) policy and for every initial level.
`S̲ = SLow G`, `S̄ = SHigh G K α`, `s̲ = sLow G K`, `s̄ = sHigh G K α` (p. 537, (21)–(23)). -/
theorem theorem4_optimal_sS_within_bounds (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (hφ0 : α * (φ 0).toReal < 1) :
    (∀ n : ℕ, 2 ≤ n →
      ∃ (Y : Policy) (sn Sn : ℤ), IsOptimal φ G K α n Y ∧ IsSSPolicy n Y ∧
        sn ≤ Sn ∧ UsesRule Y 0 sn Sn ∧
        sLow G K ≤ sn ∧ sn ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
        SLow G ≤ Sn ∧ Sn ≤ SHigh G K α) ∧
    (∃ sStar SStar : ℤ, IsInfOptimal φ G K α (stationary sStar SStar) ∧
        sLow G K ≤ sStar ∧ sStar ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
        SLow G ≤ SStar ∧ SStar ≤ SHigh G K α) := by sorry

end VeinottWagnerSS.RenewalCost.Supplement
