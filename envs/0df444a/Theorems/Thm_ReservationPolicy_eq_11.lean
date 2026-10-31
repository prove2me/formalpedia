-- Prove2me | Theorems.Thm_ReservationPolicy_eq_11
-- name    : ReservationPolicy.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:25:03.509679+00:00
-- url     : https://prove2.me/theorems/74fd8503-5fba-4b2b-ac14-67384c91a051
-- title:
--   Equation (11) — group effort at a given cutoff (corrected: effort domain)
-- statement:
--   Let $(k,\phi,\alpha,z,\kappa)$ satisfy the standing assumptions and let $d$ be a cutoff. A common effort $e$ and reward $r$ of a group of students are consistent (best response to $(d,r)$, and $r$ the expected ability of the admitted students) if and only if $e$ is an admissible effort and
--   $$
--   e=\frac{1+d}{8k-1},\ r=\frac{1+d+e}{2}\quad\text{(type $x$, investing)},\qquad
--   e=\frac{(1+d)\phi}{8k-\phi^2},\ r=\frac{1+d+\phi e}{2}\quad\text{(not investing)}.
--   $$
--   This reduces the equilibrium to one unknown, the cutoff.
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
--   - generalization: (11) derived as a necessary condition → an equivalence; reason: the page's direction is the forward implication; the converse states that the first-order solution is a best response
--   - generalization: a cutoff d ∈ (0,1) (p.9) → every real cutoff d; reason: the effort sets carry the interiority (4) needs, so the equivalence holds at every d; at d ∈ (0,1) it is the page's (11)
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (11), p.13

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_InvestGroup
import Definitions.Def_ReservationPolicy_PlainGroup

namespace ReservationPolicy

/-- **Equation (11).** At a given cutoff, the consistent effort and reward of a group are determined:
effort `(1+d)/(8k−1)` for an investing group and `(1+d)ϕ/(8k−ϕ²)` for a non-investing one, with the
reward of (10). Conversely these values are consistent whenever the effort lies in the group's
effort set. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eq. (11), p.13 (PDF 13). -/
theorem eq_11 (P : Params) (hP : P.Valid) (d : ℝ) :
    (∀ e r, InvestGroup P e d r ↔
      e ∈ investEfforts d ∧ e = (1 + d) / (8 * P.k - 1) ∧ r = (1 + d + e) / 2) ∧
    (∀ e r, PlainGroup P e d r ↔
      e ∈ plainEfforts P d ∧ e = (1 + d) * P.ϕ / (8 * P.k - P.ϕ ^ 2) ∧
        r = (1 + d + P.ϕ * e) / 2) := by sorry

end ReservationPolicy
