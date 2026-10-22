-- Prove2me | Theorems.Thm_SearchDiscovery_Reservation_discovery_value_gittins_index
-- name    : SearchDiscovery.Reservation.discovery_value_gittins_index
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:44.637981+00:00
-- url     : https://prove2.me/theorems/18ac5027-d0cd-4213-b97f-7ddd7ad0a268
-- title:
--   Proof of Theorem 1, p. 38 — z^d = g^d_t: below the discovery value, discovering strictly beats the outside option
-- statement:
--   Let $z^d$ satisfy $Q_d(c_d,c_s,z^d)=0$, (10). In the problem with an outside option offering $w$, no products, and discovery available, if $w<z^d$ then some feasible policy strictly beats taking the outside option:
--   $$w<z^d\ \Longrightarrow\ \exists\ \text{feasible }\rho:\ V(\Omega_t,\{b0,d\};\rho)>w .$$
--
--   Together with the previous milestone ($\Theta(\Omega_t,\{d\},w)=w$ for $w\ge z^d$), this says that $z^d$ is exactly the outside option at which the consumer is indifferent about discovering, i.e. the Gittins index $g^d_t$ of the discovery action, whatever the belief $q$.
-- source:
--   Greminger, Optimal Search and Discovery, arXiv:1911.07773v5, p. 38, Appendix A.1 (proof of Theorem 1), "Finally, … implies z^d = g^d_t"

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

namespace SearchDiscovery.Reservation

open MeasureTheory ProbabilityTheory

theorem discovery_value_gittins_index (M : SDModel) (hM : M.Standing)
    (zd : ℝ) (hzd : M.Qd zd = 0) (w : ℝ) (hw : w < zd) :
    ∃ ρ : InfoState → Act, M.Feasible ρ ⟨[w], [], true⟩ ∧
      w < M.value ρ ⟨[w], [], true⟩ := by sorry

end SearchDiscovery.Reservation
