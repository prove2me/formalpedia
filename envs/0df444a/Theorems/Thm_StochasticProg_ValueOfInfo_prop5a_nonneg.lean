-- Prove2me | Theorems.Thm_StochasticProg_ValueOfInfo_prop5a_nonneg
-- name    : StochasticProg.ValueOfInfo.prop5a_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:52:13.129593+00:00
-- url     : https://prove2.me/theorems/977e378c-9974-49cc-bce1-ff9e50762b1e
-- title:
--   Chapter 4, Proposition 5(a) — 0 ≤ EVPI, 0 ≤ VSS
-- statement:
--   This is part (a) of Chapter 4, Proposition 5 (pp. 167-168) of Birge & Louveaux,
--   *Introduction to Stochastic Programming*.
--
--   Let $I$ be a two-stage stochastic program with fixed recourse and finitely many scenarios
--   (an `Instance`), and let $\bar x$ be feasible ($\bar x \in K_1$) and optimal for the
--   expected-value problem at the mean scenario $\bar\xi$, i.e. $z(\bar x,\bar\xi) = EV$.
--
--   The conclusion is that, for any such stochastic program,
--   $$
--   0 \le EVPI \qquad\text{and}\qquad 0 \le VSS,
--   $$
--   where $EVPI = RP - WS$ is the expected value of perfect information and
--   $VSS = \mathbb E_\xi\,z(\bar x,\xi) - RP$ is the value of the stochastic solution relative
--   to $\bar x$.
--
--   Both nonnegativity facts follow from Proposition 1's chain $WS\le RP\le EEV$: $EVPI\ge 0$
--   from $WS\le RP$, and $VSS\ge0$ from $RP\le EEV$. They are the source of the leftmost "$0\le$"
--   link of Theorem 9's capstone inequality chain, generalized there from the mean scenario
--   $\bar\xi$ to an arbitrary reference scenario.
--
--   **Formalization Note** This item formalizes only part (a) of Proposition 5. Part (b) — the
--   upper bounds $EVPI \le EEV-EV$ and $VSS \le EEV-EV$ "for stochastic programs with fixed
--   recourse matrix and fixed objective coefficients" — needs that structural hypothesis on the
--   underlying LP data ($W$, $c$, $q$ fixed across scenarios), which is not visible once the
--   scenario cost $z$ is treated as a primitive function (as this mission's `Instance` does); it
--   is out of this mission's scope and is not needed for the goal theorem, which uses only part
--   (a).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, pp. 167-168, Chapter 4, Proposition 5(a) (eq. 4.1, 4.2)

import Mathlib
import Definitions.Def_StochasticProg_ValueOfInfo_Instance
import Definitions.Def_StochasticProg_ValueOfInfo_RP

namespace StochasticProg.ValueOfInfo

/-- Chapter 4, Proposition 5(a) (pp. 167-168): for any stochastic program,
`0 ≤ EVPI` and `0 ≤ VSS`. -/
theorem prop5a_nonneg {n1 d K : ℕ} (I : Instance n1 d K)
    (xBar : Fin n1 → ℝ) (hxBar_mem : xBar ∈ I.K1)
    (hxBar_opt : I.z xBar (xiBar I) = EV I) :
    (0 : EReal) ≤ EVPI I ∧ (0 : EReal) ≤ VSS I xBar := by sorry

end StochasticProg.ValueOfInfo
