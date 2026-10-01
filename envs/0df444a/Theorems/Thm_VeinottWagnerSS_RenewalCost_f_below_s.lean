-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_f_below_s
-- name    : VeinottWagnerSS.RenewalCost.f_below_s
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T13:17:33.901526+00:00
-- url     : https://prove2.me/theorems/6c3c30d7-a398-41fb-9a14-83eec69c5fef
-- title:
--   §3, p. 533 — $f(x) = K + f(S)$ for $x < s$
-- statement:
--   Let $\varphi$ be a demand distribution, $0 \le \alpha < 1$, $K \ge 0$, $G_\alpha : \mathbb Z \to \mathbb R$, and integers $s \le S$. If the stationary $(s, S)$ policy is started from stock $x < s$, its total expected discounted cost is
--   $$f(x \mid s, S) = K + f(S \mid s, S).$$
--
--   Below $s$ the policy orders immediately up to $S$, paying the set-up cost $K$, and thereafter behaves as if started at $S$.
--
--   **Formalization Note** $f$ is the expected cost of the controlled chain (definition `fCost`). No convexity or coercivity of $G_\alpha$ is assumed.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 533, §3, display f(x) = K + f(S), x < s

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions
import Definitions.Def_VeinottWagnerSS_RenewalCost_PolicyCost

namespace VeinottWagnerSS.RenewalCost

/-- Veinott & Wagner (1965), §3, p. 533: for `0 ≤ α < 1`, `K ≥ 0` and integers `s ≤ S`, if
`X₁ = x < s` then `f(x) = K + f(S)`. -/
theorem f_below_s (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hK : 0 ≤ K)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) (hx : x < s) :
    fCost D α K G s S x = K + fCost D α K G s S S := by sorry

end VeinottWagnerSS.RenewalCost
