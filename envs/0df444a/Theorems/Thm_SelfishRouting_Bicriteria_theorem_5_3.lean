-- Prove2me | Theorems.Thm_SelfishRouting_Bicriteria_theorem_5_3
-- name    : SelfishRouting.Bicriteria.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:28.112723+00:00
-- url     : https://prove2.me/theorems/6599ada0-badd-4eec-a40b-5851fe68aef4
-- title:
--   Theorem 5.3 — $C(f) \le \frac{1+\epsilon}{1-\epsilon} C(f^*)$ for an $\epsilon$-approximate Nash flow
-- statement:
--   Consider a routing instance with a $0/1$ edge–route incidence matrix, rates $r_i > 0$, and edge latency functions that are nonnegative, nondecreasing and continuous on $[0,\infty)$, and let $0 < \epsilon < 1$. If $f$ is at $\epsilon$-approximate Nash equilibrium for the rates $r$ and $f^*$ is any flow feasible for the rates $2r$, then
--   $$
--   C(f) \le \frac{1+\epsilon}{1-\epsilon}\, C(f^*).
--   $$
--
--   This extends Theorem 3.1 to users who evaluate latencies only up to a factor $1+\epsilon$; the paper states that the factor cannot be improved.
--
--   **Formalization Note.** $\epsilon > 0$ is the standing assumption of §5.1 (p. 19) and $\epsilon < 1$ is the theorem's own; with both, the factor is a positive real number. The paper omits the proof ("closely follows the proof of Theorem 3.1"). Same model conventions as Theorem 3.1.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 19, Theorem 5.3

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model
import Definitions.Def_SelfishRouting_Bicriteria_ApproxNash

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- Theorem 5.3 (p. 19): for `0 < ε < 1`, the cost of an `ε`-approximate Nash flow for rates
`r` is at most `(1 + ε)/(1 − ε)` times the cost of any flow feasible for the rates `2r`. -/
theorem theorem_5_3 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (x y : Fin R → ℝ) (hx : IsApproxNashFlow A s ℓ rate ε x)
    (hy : y ∈ wardropFeasible s (fun i => 2 * rate i)) :
    cost A ℓ x ≤ (1 + ε) / (1 - ε) * cost A ℓ y := by sorry

end SelfishRouting.Bicriteria
