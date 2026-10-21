-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_eq_9
-- name    : TestDistancing.Equilibrium.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:08.483026+00:00
-- url     : https://prove2.me/theorems/870a40c7-93f8-495a-b280-53b5b1c1fcf1
-- title:
--   Equation (9) and low-type equilibrium infection, corrected sign
-- statement:
--   Suppose $0<g<1$ and $(g,1)$ is a symmetric equilibrium under policy $\alpha$. Every low-value agent $l$ is indifferent between zero and one activity, so
--
--   $$P_l^{\mathrm{inf}}(1;g,\alpha)=\frac1n+v_L,\qquad P_l^{\mathrm{eq}}(g,\alpha)=g v_L+\frac1n.$$
--
--   The first identity is (9), and the second averages over the agent's own Bernoulli action. **Formalization Note** The paper prints a minus sign in the second identity; direct expansion gives the plus sign shown here.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, p. 37 (PDF 39), (9) and following calculation

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

theorem eq_9 (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (α : ℝ × ℝ) (hα : α ∈ PolicySquare) (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1)
    (heq : IsSymEq P n (g, 1) α) (l : Fin n) (hl : ¬ IsHigh P l) :
    PinfMix P (g, 1) α l 1 = (1 : ℝ) / n + P.vL ∧
    eqInf P (g, 1) α l = g * P.vL + (1 : ℝ) / n := by sorry

end TestDistancing.Equilibrium
