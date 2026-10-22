-- Prove2me | Theorems.Thm_SearchDiscovery_Reservation_discovery_outside_option_retire
-- name    : SearchDiscovery.Reservation.discovery_outside_option_retire
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:40.933916+00:00
-- url     : https://prove2.me/theorems/2d423a9e-a314-4e3a-ad78-874035d6a08f
-- title:
--   Proof of Theorem 1, p. 37 — Θ(Ω_t, {d}, w) = w for every outside option w ≥ z^d
-- statement:
--   Let $z^d$ satisfy $Q_d(c_d,c_s,z^d)=0$, (10). Consider the problem $\Theta(\Omega_t,\{d\},w)$ in which the consumer holds an outside option offering $w$, no products, and the option to discover (later discoveries remain available according to the belief $q$). If $w\ge z^d$, then no feasible policy does better than taking the outside option at once:
--   $$w\ge z^d\ \Longrightarrow\ V(\Omega_t,\{b0,d\};\rho)\le w\quad\text{for every feasible policy }\rho,$$
--   so that $\Theta(\Omega_t,\{d\},w)=w$.
--
--   This is the step of the proof of Theorem 1 that makes the index of discovery independent of the availability of future discoveries and of $q$.
--
--   **Formalization Note.** The paper states the identity for $w\ge g^d_{t+1}$; with $g^d=z^d$ (the companion milestone and p. 38) this is $w\ge z^d$. The initial state has discovery available; later availability is drawn from the Bernoulli($q$) flags.
-- source:
--   Greminger, Optimal Search and Discovery, arXiv:1911.07773v5, p. 37, Appendix A.1 (proof of Theorem 1), paragraph after (23)

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

namespace SearchDiscovery.Reservation

open MeasureTheory ProbabilityTheory

theorem discovery_outside_option_retire (M : SDModel) (hM : M.Standing)
    (zd : ℝ) (hzd : M.Qd zd = 0) (w : ℝ) (hw : zd ≤ w) :
    ∀ ρ : InfoState → Act, M.Feasible ρ ⟨[w], [], true⟩ →
      M.value ρ ⟨[w], [], true⟩ ≤ w := by sorry

end SearchDiscovery.Reservation
