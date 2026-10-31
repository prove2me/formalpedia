-- Prove2me | Theorems.Thm_RandomPIGame_section2_value
-- name    : RandomPIGame.section2_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:34.304973+00:00
-- url     : https://prove2.me/theorems/6d8217f5-b311-4990-9cbb-8a0a959388c4
-- title:
--   §2, p.9: every game has a value, $\sup\inf=\inf\sup$
-- statement:
--   Every game $\omega\in\Omega$ has a value:
--   $$
--   \sup_{\sigma_{\mathrm I}}\inf_{\sigma_{\mathrm{II}}}u_\omega(\sigma_{\mathrm I},\sigma_{\mathrm{II}})=\inf_{\sigma_{\mathrm{II}}}\sup_{\sigma_{\mathrm I}}u_\omega(\sigma_{\mathrm I},\sigma_{\mathrm{II}}).
--   $$
--
--   The value is the highest payoff Player I can guarantee and the lowest payoff Player II can force, so that "the value of the random game" is a well-defined quantity. The paper derives this from Martin's determinacy theorem; the statement here concerns these games only.
--
--   Differences from the source:
--   - encoding: a play is a finite or infinite sequence of nodes, and the payoff is the infimum of its capacities → a play is a sequence indexed by ℕ that stays at an end node once reached, and the payoff is the infimum over all stages; reason: stuttering does not change the set of capacities visited
--   - encoding: capacities and thresholds k in [0, ∞) → capacities and thresholds k in ℝ≥0; reason: Lean convention; the same numbers
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, §2, p.9, display "vω =: sup inf uω(σI, σII) = inf sup uω(σI, σII)"

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game
import Definitions.Def_RandomPIGame_Value

namespace RandomPIGame

/-- Every game `ω` has a value: `sup_{σ_I} inf_{σ_II} u_ω = inf_{σ_II} sup_{σ_I} u_ω`.
arXiv:2104.10528v1, §2, p.9, display "v_ω =: sup inf … = inf sup …". -/
theorem section2_value (ω : Game) :
    ω.value = ⨅ σII : ω.Strategy Player.II, ⨆ σI : ω.Strategy Player.I, ω.payoff σI σII := by sorry

end RandomPIGame
