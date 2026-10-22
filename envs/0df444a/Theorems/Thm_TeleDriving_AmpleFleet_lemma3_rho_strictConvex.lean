-- Prove2me | Theorems.Thm_TeleDriving_AmpleFleet_lemma3_rho_strictConvex
-- name    : TeleDriving.AmpleFleet.lemma3_rho_strictConvex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:28.224977+00:00
-- url     : https://prove2.me/theorems/47f20325-6246-49db-b7c1-b5860d368ddc
-- title:
--   Lemma 3 (first sentence), p. 37 — ρ(q) is strictly convex and 1/ρ(q) strictly concave on [1, m]
-- statement:
--   Consider the ride-hailing loss model with $m$ vehicles, arrival rate $\lambda$ and service rate $\mu(m,q)$ satisfying Assumptions 1 and 2 and the size restriction $m \ge \bar m$, $\lambda > \max\{1/s, \max_{q \le \bar m} q\mu(\bar m, q)\}$. Let $\rho(q) = \lambda/(q\,\mu(m,q))$. Then on $[1,m]$
--
--   $$q \mapsto \rho(q) \ \text{is strictly convex}, \qquad q \mapsto \frac{1}{\rho(q)} = \frac{q\,\mu(m,q)}{\lambda} \ \text{is strictly concave}.$$
--
--   Convexity of $\rho$ is what makes the set where $\rho < 1$ an interval, which in turn yields the three regimes of the model and the shape of the service level in the number of drivers.
--
--   **Formalization Note** The statement is about $q$ real in $[1,m]$; no differentiability of $\mu$ is assumed, although the paper's proof differentiates twice. The standing hypotheses are carried as in every statement of this paper; no regime is assumed.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 37, Lemma 3 (first sentence)

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AmpleFleet

theorem lemma3_rho_strictConvex (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : TeleDriving.ScarceFleet.Assumption1 mu s)
    (hA2 : TeleDriving.ScarceFleet.Assumption2 mu mbar) (hsize : TeleDriving.ScarceFleet.StandingSize mu s mbar m lam) :
    StrictConvexOn ℝ (Set.Icc (1 : ℝ) m) (TeleDriving.ScarceFleet.rho mu lam m) ∧
      StrictConcaveOn ℝ (Set.Icc (1 : ℝ) m) (fun q => 1 / TeleDriving.ScarceFleet.rho mu lam m q) := by sorry

end TeleDriving.AmpleFleet
