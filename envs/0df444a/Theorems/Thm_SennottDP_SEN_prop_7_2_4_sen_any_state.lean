-- Prove2me | Theorems.Thm_SennottDP_SEN_prop_7_2_4_sen_any_state
-- name    : SennottDP.SEN.prop_7_2_4_sen_any_state
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T10:29:11.403347+00:00
-- url     : https://prove2.me/theorems/f2a7b7b9-a755-4965-ae78-b59679d95b41
-- title:
--   Proposition 7.2.4 — (SEN) does not depend on the choice of distinguished state
-- statement:
--   Assume that the (SEN) assumptions hold for a distinguished state $z$ (with some function $M$ and constant $L$). Then for every other state $x$ the (SEN) assumptions also hold with $x$ as the distinguished state, for some nonnegative finite function $M_x$ and some nonnegative finite constant $L_x$:
--
--   $$\text{(SEN)}_z \;\Longrightarrow\; \text{(SEN)}_x \qquad \text{for all } x \in S.$$
--
--   Verifying (SEN) therefore only requires a convenient choice of reference state.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 137, Proposition 7.2.4

import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions

namespace SennottDP.SEN

/-- Sennott (1999), Proposition 7.2.4, p. 137: assume that the (SEN) assumptions hold for a
distinguished state `z` (with some function `Mf` in (SEN2) and constant `L` in (SEN3)). Then
(SEN) holds if `z` is replaced by any other state `x`: there are a function `Mx` and a constant
`Lx` for which (SEN1)–(SEN3) hold with distinguished state `x`. -/
theorem prop_7_2_4_sen_any_state {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf : S → ℝ) (L : ℝ) (hSEN : SENAssumptions M z Mf L) (x : S) :
    ∃ (Mx : S → ℝ) (Lx : ℝ), SENAssumptions M x Mx Lx := by sorry

end SennottDP.SEN
