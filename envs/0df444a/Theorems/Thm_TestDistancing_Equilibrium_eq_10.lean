-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_eq_10
-- name    : TestDistancing.Equilibrium.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:08.317652+00:00
-- url     : https://prove2.me/theorems/78c87f7d-444a-4a99-b198-039f33205be5
-- title:
--   Equation (10) and high-type equilibrium infection, corrected sign
-- statement:
--   Suppose $0<g<1$ and $(0,g)$ is a symmetric equilibrium under policy $\alpha$. Every high-value agent $h$ is indifferent between zero and one activity, so
--
--   $$P_h^{\mathrm{inf}}(1;g,\alpha)=\frac1n+v_H,\qquad P_h^{\mathrm{eq}}(g,\alpha)=g v_H+\frac1n.$$
--
--   The first identity is (10), and the second averages over the agent's own Bernoulli action. **Formalization Note** The paper's displayed second identity has a minus sign; expansion and the main text on p. 14 give the plus sign.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, p. 38 (PDF 40), (10) and following calculation

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

theorem eq_10 (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (α : ℝ × ℝ) (hα : α ∈ PolicySquare) (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1)
    (heq : IsSymEq P n (0, g) α) (h : Fin n) (hh : IsHigh P h) :
    PinfMix P (0, g) α h 1 = (1 : ℝ) / n + P.vH ∧
    eqInf P (0, g) α h = g * P.vH + (1 : ℝ) / n := by sorry

end TestDistancing.Equilibrium
