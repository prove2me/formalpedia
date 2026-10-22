-- Prove2me | Theorems.Thm_SearchDiscovery_Reservation_search_value_gittins_index
-- name    : SearchDiscovery.Reservation.search_value_gittins_index
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:42.249657+00:00
-- url     : https://prove2.me/theorems/4d6005c5-89dc-41cf-958b-776fbe6e3391
-- title:
--   Proof of Theorem 1, p. 38 — the search and purchase values are the indifference outside options (Gittins indices) of inspection and purchase
-- statement:
--   Let $z^s$ be a search value function, i.e. $Q_s(x,c_s,z^s(x))=0$ for every $x$, (6). Consider the reduced search problem $\Theta(\Omega,\{s\},w)$ with one outside option offering $w$ and a single product with known partial valuation $x$ that may be inspected, and no discovery. Then taking the outside option is optimal exactly when the outside option is at least the search value:
--   $$\Big(\,V(\Omega_0,A_0;\rho)\le w\ \text{ for every feasible policy }\rho\,\Big)\iff z^s(x)\le w .$$
--   Since buying the outside option at once is feasible with value $w$, the left side says $\Theta(\Omega,\{s\},w)=w$.
--   Likewise, for the reduced problem with the outside option $w$ and a single inspected product of purchase value $v$ (no products to inspect, no discovery),
--   $$\Big(\,V(\Omega_0,A_0;\rho)\le w\ \text{ for every feasible policy }\rho\,\Big)\iff v\le w .$$
--
--   This identifies the search value of (6) and the purchase value of (8) with the Gittins indices of the inspection and purchase actions, as the last paragraph of the proof of Theorem 1 states.
--
--   **Formalization Note.** The page cites "(6) and (10)" for the inspection and purchase values; these are (6) and (8). The reduced states are the information states $([w],[x],\text{no discovery})$ and $([w,v],[\,],\text{no discovery})$.
-- source:
--   Greminger, Optimal Search and Discovery, arXiv:1911.07773v5, p. 38, Appendix A.1 (proof of Theorem 1), last paragraph

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

namespace SearchDiscovery.Reservation

open MeasureTheory ProbabilityTheory

theorem search_value_gittins_index (M : SDModel) (hM : M.Standing)
    (zs : ℝ → ℝ) (hzs : ∀ x, M.Qs x (zs x) = 0) (w x v : ℝ) :
    ((∀ ρ : InfoState → Act, M.Feasible ρ ⟨[w], [x], false⟩ →
        M.value ρ ⟨[w], [x], false⟩ ≤ w) ↔ zs x ≤ w) ∧
    ((∀ ρ : InfoState → Act, M.Feasible ρ ⟨[w, v], [], false⟩ →
        M.value ρ ⟨[w, v], [], false⟩ ≤ w) ↔ v ≤ w) := by sorry

end SearchDiscovery.Reservation
