-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_f_above_s
-- name    : VeinottWagnerSS.RenewalCost.f_above_s
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T13:19:43.234669+00:00
-- url     : https://prove2.me/theorems/b52884a6-c05d-4f1d-8f87-e8842b0f868e
-- title:
--   §3, p. 533 — $f(x) = L_\alpha(x, x-s) + K r_\alpha(x-s) + f(S) r_\alpha(x-s)$ for $x \ge s$
-- statement:
--   Let $\varphi$ be a demand distribution, $0 \le \alpha < 1$, $K \ge 0$, $G_\alpha : \mathbb Z \to \mathbb R$, and integers $s \le S$. If the stationary $(s, S)$ policy is started from stock $x \ge s$, its total expected discounted cost satisfies
--   $$f(x) = L_\alpha(x, x - s) + K r_\alpha(x - s) + f(S)\, r_\alpha(x - s).$$
--
--   No order is placed until cumulative demand exceeds $x - s$; then an order up to $S$ is placed and the process renews.
--
--   **Formalization Note** $x - s \ge 0$ is passed to $L_\alpha$ and $r_\alpha$ as a natural number (`(x - s).toNat`, exact because $s \le x$). $f$ is the expected cost of the controlled chain. No convexity or coercivity of $G_\alpha$ is assumed.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 533, §3, last display (x ≥ s)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions
import Definitions.Def_VeinottWagnerSS_RenewalCost_PolicyCost

namespace VeinottWagnerSS.RenewalCost

/-- Veinott & Wagner (1965), §3, p. 533: for `0 ≤ α < 1`, `K ≥ 0` and integers `s ≤ S`, if
`X₁ = x ≥ s` then `f(x) = L_α(x, x − s) + K r_α(x − s) + f(S) r_α(x − s)`. -/
theorem f_above_s (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hK : 0 ≤ K)
    (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) (hx : s ≤ x) :
    fCost D α K G s S x =
      LAlpha D.φ α G x (x - s).toNat + K * rAlpha D.φ α (x - s).toNat
        + fCost D α K G s S S * rAlpha D.φ α (x - s).toNat := by sorry

end VeinottWagnerSS.RenewalCost
