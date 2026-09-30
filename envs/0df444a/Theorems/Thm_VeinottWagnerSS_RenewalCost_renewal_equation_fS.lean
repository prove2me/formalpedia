-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_renewal_equation_fS
-- name    : VeinottWagnerSS.RenewalCost.renewal_equation_fS
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T13:12:29.708445+00:00
-- url     : https://prove2.me/theorems/1e266bf4-ebf7-4a93-a84b-62127eae702d
-- title:
--   §3, p. 533 — renewal equation $f(S) = L_\alpha(S, D) + K r_\alpha(D) + f(S) r_\alpha(D)$
-- statement:
--   Let $\varphi$ be a demand distribution, $0 \le \alpha < 1$, $K \ge 0$, $G_\alpha : \mathbb Z \to \mathbb R$, and integers $s \le S$ with $D = S - s$. Let $f(x) = f(x \mid s, S)$ be the total expected discounted cost of the stationary $(s, S)$ policy started from stock $x$. Then
--   $$f(S) = L_\alpha(S, D) + K r_\alpha(D) + f(S)\, r_\alpha(D).$$
--
--   Starting at $S$, no order is placed until cumulative demand exceeds $D$, after which the process restarts from $S$; the equation expresses this renewal.
--
--   **Formalization Note** $f$ is the expected cost of the controlled chain (definition `fCost`), not a closed form. Convexity and coercivity of $G_\alpha$, standing assumptions of the paper, are not assumed: for $\alpha < 1$ the statement holds for every $G_\alpha$.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 533, §3 (Renewal Approach), first display after Eq. (9)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions
import Definitions.Def_VeinottWagnerSS_RenewalCost_PolicyCost

namespace VeinottWagnerSS.RenewalCost

/-- Veinott & Wagner (1965), §3, p. 533: for `0 ≤ α < 1`, `K ≥ 0` and integers `s ≤ S`, with
`D = S − s`, the discounted cost of the stationary `(s, S)` policy started at `X₁ = S`
satisfies the renewal equation `f(S) = L_α(S, D) + K r_α(D) + f(S) r_α(D)`. -/
theorem renewal_equation_fS (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hK : 0 ≤ K) (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) :
    fCost D α K G s S S =
      LAlpha D.φ α G S (S - s).toNat + K * rAlpha D.φ α (S - s).toNat
        + fCost D α K G s S S * rAlpha D.φ α (S - s).toNat := by sorry

end VeinottWagnerSS.RenewalCost
