-- Prove2me | Theorems.Thm_StochasticProg_ValueOfInfo_prop1_ws_le_rp_le_eev
-- name    : StochasticProg.ValueOfInfo.prop1_ws_le_rp_le_eev
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:51:23.408885+00:00
-- url     : https://prove2.me/theorems/b5957418-1c01-4a50-9c80-34640f7d2c8b
-- title:
--   Chapter 4, Proposition 1 — WS ≤ RP ≤ EEV
-- statement:
--   This is Chapter 4, Proposition 1 (p. 166) of Birge & Louveaux, *Introduction to Stochastic
--   Programming*, the chain of inequalities first established by Madansky (1960).
--
--   Let $I$ be a two-stage stochastic program with fixed recourse and finitely many scenarios
--   (an `Instance`: first-stage feasible set $K_1$, scenario cost $z(x,\xi)$, $K$ scenarios with
--   probabilities $p_k$). Let $\bar x$ be a first-stage decision that is feasible
--   ($\bar x \in K_1$) and optimal for the expected-value problem at the mean scenario $\bar\xi$,
--   i.e. $z(\bar x,\bar\xi)$ equals $EV = \min_{x\in K_1} z(x,\bar\xi)$.
--
--   The conclusion is the chain
--   $$
--   WS \le RP \le EEV,
--   $$
--   where $WS = \mathbb E_\xi\big[\min_{x\in K_1} z(x,\xi)\big]$ is the wait-and-see value,
--   $RP = \min_{x\in K_1}\mathbb E_\xi\,z(x,\xi)$ is the recourse problem's optimal value, and
--   $EEV = \mathbb E_\xi\,z(\bar x,\xi)$ is the expected cost of implementing $\bar x$ across
--   every scenario.
--
--   This is the most basic comparison among the here-and-now, wait-and-see and expected-value
--   solutions, and both remaining gaps ($RP-WS = EVPI$, $EEV-RP = VSS$) are the two central
--   uncertainty measures of the chapter.
--
--   **Formalization Note** Both quantities take values in the extended reals
--   $\overline{\mathbb R}$, so the inequalities hold in the complete linear order on
--   $\overline{\mathbb R}$ (where $-\infty$ and $+\infty$ are legitimate values, e.g. when $K_1$
--   admits no feasible point for some scenario).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 166, Chapter 4, Proposition 1 (eq. 3.1)

import Mathlib
import Definitions.Def_StochasticProg_ValueOfInfo_Instance
import Definitions.Def_StochasticProg_ValueOfInfo_RP

namespace StochasticProg.ValueOfInfo

/-- Chapter 4, Proposition 1 (p. 166): `WS ≤ RP ≤ EEV`. -/
theorem prop1_ws_le_rp_le_eev {n1 d K : ℕ} (I : Instance n1 d K)
    (xBar : Fin n1 → ℝ) (hxBar_mem : xBar ∈ I.K1)
    (hxBar_opt : I.z xBar (xiBar I) = EV I) :
    WS I ≤ RP I ∧ RP I ≤ EEV I xBar := by sorry

end StochasticProg.ValueOfInfo
