-- Prove2me | Theorems.Thm_RandomPIGame_section2_optimal_strategies
-- name    : RandomPIGame.section2_optimal_strategies
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:27.167999+00:00
-- url     : https://prove2.me/theorems/324b49f5-81d6-4aa7-93d9-88661821c888
-- title:
--   §2, p.9: Player I has a $v_\omega$-optimal strategy; Player II has a $(v_\omega+\varepsilon)$-optimal one
-- statement:
--   Let $\omega\in\Omega$. Player I has a $v_\omega$-optimal strategy: there is $\sigma_{\mathrm I}$ with $u_\omega(\sigma_{\mathrm I},\sigma_{\mathrm{II}})\ge v_\omega$ for every $\sigma_{\mathrm{II}}$. For each $\varepsilon>0$, Player II has a $(v_\omega+\varepsilon)$-optimal strategy: there is $\sigma_{\mathrm{II}}$ with $u_\omega(\sigma_{\mathrm I},\sigma_{\mathrm{II}})\le v_\omega+\varepsilon$ for every $\sigma_{\mathrm I}$.
--
--   The asymmetry between the players reflects the upper semicontinuity of the payoff. These strategies carry the comparison between a game and its truncations.
--
--   Differences from the source:
--   - encoding: a play is a finite or infinite sequence of nodes, and the payoff is the infimum of its capacities → a play is a sequence indexed by ℕ that stays at an end node once reached, and the payoff is the infimum over all stages; reason: stuttering does not change the set of capacities visited
--   - encoding: v_ω is the common value of sup inf and inf sup → value is defined as the sup inf; reason: the equality with inf sup is the milestone section2_value; the strategy types are nonempty and payoffs lie in [0, γ(⊘)], so both real extrema are genuine
--   - encoding: capacities and thresholds k in [0, ∞) → capacities and thresholds k in ℝ≥0; reason: Lean convention; the same numbers
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, §2, p.9

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game
import Definitions.Def_RandomPIGame_Value

namespace RandomPIGame

/-- In each game `ω`, Player I has a `v_ω`-optimal strategy, and Player II has a
`(v_ω + ε)`-optimal strategy for each `ε > 0`. arXiv:2104.10528v1, §2, p.9. -/
theorem section2_optimal_strategies (ω : Game) :
    (∃ σI : ω.Strategy Player.I, ω.IsOptimalI ω.value σI) ∧
      ∀ ε : ℝ, 0 < ε → ∃ σII : ω.Strategy Player.II, ω.IsOptimalII (ω.value + ε) σII := by sorry

end RandomPIGame
