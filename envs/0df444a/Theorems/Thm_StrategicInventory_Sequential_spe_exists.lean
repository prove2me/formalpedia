-- Prove2me | Theorems.Thm_StrategicInventory_Sequential_spe_exists
-- name    : StrategicInventory.Sequential.spe_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:07:32.251753+00:00
-- url     : https://prove2.me/theorems/20fe36f1-8e60-4b06-a580-cf58dc86a27b
-- title:
--   Proposition 4.1 (existence) — the sequential model has a subgame perfect equilibrium for every $h \ge 0$, $s \ge 0$
-- statement:
--   For every demand intercept $\alpha > 0$, every holding cost $h \ge 0$ and every direct selling cost $s \ge 0$, the sequential two-period game between the supplier and the buyer has a subgame perfect equilibrium:
--
--   $$
--   \exists\, \sigma \ \text{ such that } \ \sigma \text{ is a subgame perfect equilibrium for } (\alpha, h, s).
--   $$
--
--   Existence underlies every equilibrium statement of the paper. The equilibrium tables of Appendix A describe the equilibrium in each region of the $(h, s)$ plane.
--
--   **Formalization Note.** Proposition 4.1 of the paper also asserts uniqueness. Uniqueness is not stated here. As a statement about strategy profiles it is false: after the off-path price $w_2 = 0$, every order $Q_2 \ge q_2 - I$ is optimal for the buyer. It may also fail for the equilibrium path at points where the supplier is indifferent between two first-period prices, for example on the boundary $h = h_{11}$ between Regions 7 and 8.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, p. 542, Proposition 4.1

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE

namespace StrategicInventory.Sequential

/-- Proposition 4.1, p. 542 (existence half): for any `h ≥ 0` and `s ≥ 0`
(and any demand intercept `α > 0`) the sequential model has a subgame perfect
equilibrium. The paper's uniqueness claim is not stated. -/
theorem spe_exists (α h s : ℝ) (hα : 0 < α) (hh : 0 ≤ h) (hs : 0 ≤ s) :
    ∃ σ : Profile, IsSPE α h s σ := by sorry

end StrategicInventory.Sequential
