-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_eq11_aCost_closed_form
-- name    : VeinottWagnerSS.RenewalCost.eq11_aCost_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T13:27:59.044978+00:00
-- url     : https://prove2.me/theorems/c3f8f052-b2a8-4689-b3df-29e2e145f339
-- title:
--   Eq. (11) — closed form of the cost per period $a_\alpha(x \mid s, S)$ of a stationary $(s, S)$ policy
-- statement:
--   Let the demands be i.i.d. with distribution $\varphi$ on $\{0, 1, \dots\}$, let $0 \le \alpha < 1$ be the discount factor, $K \ge 0$ the set-up cost and $G_\alpha : \mathbb Z \to \mathbb R$ the one-period cost, and let $s \le S$ be integers with $D = S - s$. Let $a_\alpha(x) = (1 - \alpha) f(x \mid s, S)$ be the equivalent cost per period of the stationary $(s, S)$ policy started from stock $x$, where $f$ is its total expected discounted cost. Then
--   $$a_\alpha(x) = \begin{cases} \dfrac{L_\alpha(S, D) + K}{1 + M_\alpha(D)} & x < s, \\[2ex] (1 - \alpha) L_\alpha(x, x - s) + \dfrac{L_\alpha(S, D) + K}{1 + M_\alpha(D)}\, r_\alpha(x - s) & x \ge s, \end{cases}$$
--   with $L_\alpha$ given by (7), $M_\alpha$ the discount renewal function and $r_\alpha(d) = E[\alpha^{T(d)}]$.
--
--   This is the criterion minimized by the paper's algorithm for computing an optimal $(s, S)$ policy (Section 4).
--
--   **Formalization Note** The model is the paper's reduced model (Eq. (2)): unit purchase cost $0$ and one-period cost $G_\alpha$. $f$ is the expected cost of the controlled Markov chain, not a closed form. $L_\alpha$ and $r_\alpha$ are defined by their series ((7) and the first line of (9)). $x - s$ and $D$ are passed as natural numbers via `toNat`. The paper's standing assumptions that $G_\alpha$ is convex and tends to $+\infty$ at $\pm\infty$ are not assumed; for $\alpha < 1$ the identity holds for every $G_\alpha$.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 534, Eq. (11)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions
import Definitions.Def_VeinottWagnerSS_RenewalCost_PolicyCost

namespace VeinottWagnerSS.RenewalCost

/-- Veinott & Wagner (1965), Eq. (11), p. 534: for `0 ≤ α < 1`, `K ≥ 0`, integers `s ≤ S` and
`D = S − s`, the equivalent cost per period `a_α(x) = (1 − α) f(x | s, S)` of the stationary
`(s, S)` policy is
`a_α(x) = (L_α(S, D) + K)/(1 + M_α(D))` for `x < s` and
`a_α(x) = (1 − α) L_α(x, x − s) + [(L_α(S, D) + K)/(1 + M_α(D))] r_α(x − s)` for `x ≥ s`. -/
theorem eq11_aCost_closed_form (D : DemandDist) (α K : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hK : 0 ≤ K) (G : ℤ → ℝ) (s S : ℤ) (hsS : s ≤ S) (x : ℤ) :
    aCost D α K G s S x =
      if x < s then
        (LAlpha D.φ α G S (S - s).toNat + K) / (1 + MAlpha D.φ α (S - s).toNat)
      else
        (1 - α) * LAlpha D.φ α G x (x - s).toNat
          + (LAlpha D.φ α G S (S - s).toNat + K) / (1 + MAlpha D.φ α (S - s).toNat)
            * rAlpha D.φ α (x - s).toNat := by sorry

end VeinottWagnerSS.RenewalCost
