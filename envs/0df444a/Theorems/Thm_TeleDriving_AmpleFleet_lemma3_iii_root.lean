-- Prove2me | Theorems.Thm_TeleDriving_AmpleFleet_lemma3_iii_root
-- name    : TeleDriving.AmpleFleet.lemma3_iii_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:46.426979+00:00
-- url     : https://prove2.me/theorems/bed5331d-0f02-460b-b964-634f030ce295
-- title:
--   Lemma 3(iii), p. 37 — in the supply-rich regime ρ(q) = 1 has a unique root q₃ ∈ (1, m), with ρ < 1 exactly to its right
-- statement:
--   In the ride-hailing loss model under Assumptions 1–2 and the size restriction, suppose the system is **supply-rich**: $\rho(m) < 1$, i.e. $\lambda < m\,\mu(m,m)$ (the case $m > \gamma_2(\lambda)$). Then there is $q_3 \in (1,m)$ such that for every $q \in [1,m]$
--
--   $$\rho(q) < 1 \iff q > q_3, \qquad \rho(q) = 1 \iff q = q_3 .$$
--
--   In particular $\rho(q) \ge 1$ for $q \le q_3$, with equality only at $q_3$. The threshold $q_3$ is the point beyond which the stationary probabilities $\pi_{m,n}(q)$ decrease in $q$, and it enters the lower bound on the service level in Theorem 1.C.
--
--   **Formalization Note** The regime $m > \gamma_2(\lambda)$ is encoded by its characterization $\rho(m) < 1$ from the proof of Lemma 3 (item (2), p. 37). The root is asserted to lie in the open interval $(1,m)$, which the paper's proof gives since $\rho(1) > 1$ (from $\lambda > 1/s$) and $\rho(m) < 1$.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 37, Lemma 3(iii); proof p. 38, Case (iii)

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AmpleFleet

theorem lemma3_iii_root (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : TeleDriving.ScarceFleet.Assumption1 mu s)
    (hA2 : TeleDriving.ScarceFleet.Assumption2 mu mbar) (hsize : TeleDriving.ScarceFleet.StandingSize mu s mbar m lam)
    (hreg : TeleDriving.ScarceFleet.IsSupplyRich mu lam m) :
    ∃ q3 ∈ Set.Ioo (1 : ℝ) m, ∀ q ∈ Set.Icc (1 : ℝ) m,
      (TeleDriving.ScarceFleet.rho mu lam m q < 1 ↔ q3 < q) ∧ (TeleDriving.ScarceFleet.rho mu lam m q = 1 ↔ q = q3) := by sorry

end TeleDriving.AmpleFleet
