-- Prove2me | Theorems.Thm_TeleDriving_ScarceFleet_lemma3_rho_strictConvex
-- name    : TeleDriving.ScarceFleet.lemma3_rho_strictConvex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:05.878216+00:00
-- url     : https://prove2.me/theorems/32520eee-cc83-4e9c-a951-1445669483d2
-- title:
--   Lemma 3, p. 37 — ρ(q) is strictly convex and 1/ρ(q) is strictly concave on [1, m]
-- statement:
--   Let $\mu(m, q)$ satisfy Assumptions 1 and 2, and let $m$ and $\lambda$ satisfy the size restriction $m \ge \bar m$, $\lambda > \max\{1/s, \max_{q \le \bar m} q\mu(\bar m, q)\}$. Then the ratio of the arrival rate to the trip-completion rate,
--   $$\rho(q) = \frac{\lambda}{q\,\mu(m,q)},$$
--   is strictly convex in the real variable $q \in [1, m]$, and its reciprocal $1/\rho(q) = q\mu(m,q)/\lambda$ is strictly concave on $[1, m]$.
--
--   This is the shape result behind the paper's three regimes and behind every monotonicity argument for the service level: it makes $\rho$ increasing to the right of any point where it has increased once.
--
--   **Formalization Note** Only the first sentence of Lemma 3 is stated here; the regime part (i)–(iii) is encoded in the definitions. The standing assumptions of pp. 11 and 13 are hypotheses although the claim needs only Assumption 1 and $\lambda > 0$. The page's proof differentiates twice; the statement makes no differentiability assumption.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 37, Lemma 3 (first sentence); proof p. 37

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.ScarceFleet

theorem lemma3_rho_strictConvex (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hA2 : Assumption2 mu mbar) (hsize : StandingSize mu s mbar m lam) :
    StrictConvexOn ℝ (Set.Icc (1 : ℝ) m) (rho mu lam m) ∧
      StrictConcaveOn ℝ (Set.Icc (1 : ℝ) m) (fun q => 1 / rho mu lam m q) := by sorry

end TeleDriving.ScarceFleet
