-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_eq10_fCost_closed_form
-- name    : VeinottWagnerSS.RenewalCost.eq10_fCost_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T13:24:44.829752+00:00
-- url     : https://prove2.me/theorems/d6cb3d68-092a-4d7b-b971-9136f1e1cd19
-- title:
--   Eq. (10) — closed form of the discounted cost $f(x \mid s, S)$ of a stationary $(s, S)$ policy
-- statement:
--   Let $\varphi$ be a demand distribution, $0 \le \alpha < 1$, $K \ge 0$, $G_\alpha : \mathbb Z \to \mathbb R$, and integers $s \le S$ with $D = S - s$. The total expected discounted cost of the stationary $(s, S)$ policy started from stock $x$ is
--   $$f(x) = \begin{cases} \dfrac{L_\alpha(S, D) + K}{1 - r_\alpha(D)} & x < s, \\[2ex] L_\alpha(x, x - s) + \dfrac{L_\alpha(S, D) + K}{1 - r_\alpha(D)}\, r_\alpha(x - s) & x \ge s. \end{cases}$$
--
--   It expresses the infinite-horizon cost of any $(s, S)$ policy through finitely computable renewal quantities.
--
--   **Formalization Note** The denominator $1 - r_\alpha(D) = (1-\alpha)(1 + M_\alpha(D))$ is positive for $\alpha < 1$; the statement does not rely on Lean's convention $y/0 = 0$. $x - s$ and $D$ are passed as natural numbers via `toNat`. No convexity or coercivity of $G_\alpha$ is assumed.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 534, Eq. (10)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions
import Definitions.Def_VeinottWagnerSS_RenewalCost_PolicyCost

namespace VeinottWagnerSS.RenewalCost

/-- Veinott & Wagner (1965), Eq. (10), p. 534: for `0 ≤ α < 1`, `K ≥ 0`, integers `s ≤ S` and
`D = S − s`, the discounted cost of the stationary `(s, S)` policy is
`f(x) = (L_α(S, D) + K)/(1 − r_α(D))` for `x < s` and
`f(x) = L_α(x, x − s) + [(L_α(S, D) + K)/(1 − r_α(D))] r_α(x − s)` for `x ≥ s`. -/
theorem eq10_fCost_closed_form (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hK : 0 ≤ K) (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) :
    fCost D α K G s S x =
      if x < s then
        (LAlpha D.φ α G S (S - s).toNat + K) / (1 - rAlpha D.φ α (S - s).toNat)
      else
        LAlpha D.φ α G x (x - s).toNat
          + (LAlpha D.φ α G S (S - s).toNat + K) / (1 - rAlpha D.φ α (S - s).toNat)
            * rAlpha D.φ α (x - s).toNat := by sorry

end VeinottWagnerSS.RenewalCost
