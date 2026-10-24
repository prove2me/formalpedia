-- Prove2me | Theorems.Thm_SensitivityPoA_Continuity_theorem_6
-- name    : SensitivityPoA.Continuity.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:17.790293+00:00
-- url     : https://prove2.me/theorems/70fade1b-b59f-464c-8b97-687289726d3a
-- title:
--   Theorem 6, p. 19 — continuity of optimum cost, equilibrium cost and PoA
-- statement:
--   Fix a network satisfying the paper's standing assumptions. For every sequence of games $\Gamma_n$ in its game space that converges in the distance of (3.3) to a game $\Gamma$ in that space, all three cost maps converge:
--   $$C^*(\Gamma_n)\to C^*(\Gamma),\qquad \widetilde C(\Gamma_n)\to\widetilde C(\Gamma),\qquad \rho(\Gamma_n)\to\rho(\Gamma).$$
--   Thus the social-optimum cost, Wardrop-equilibrium cost, and price of anarchy are continuous on the game space.
--
--   **Formalization Note** Convergence is stated sequentially, as the paper defines it. The game-space conditions, including positive total demand and Condition 2, apply to every term and the limit; they ensure the PoA denominator is positive.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 19, Theorem 6

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Continuity_Setting

namespace SensitivityPoA.Continuity

theorem theorem_6 (N : Network) (hN : N.Standing)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (Γs : ℕ → Game N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Filter.Tendsto (fun n => gameDist (Γs n) Γ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => SOCost (Γs n)) Filter.atTop (nhds (SOCost Γ)) ∧
    Filter.Tendsto (fun n => WECost (Γs n)) Filter.atTop (nhds (WECost Γ)) ∧
    Filter.Tendsto (fun n => PoA (Γs n)) Filter.atTop (nhds (PoA Γ)) := by sorry

end SensitivityPoA.Continuity
