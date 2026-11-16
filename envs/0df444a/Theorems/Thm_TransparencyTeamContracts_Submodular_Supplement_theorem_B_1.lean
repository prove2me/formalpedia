-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_theorem_B_1
-- name    : TransparencyTeamContracts.Submodular.Supplement.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:22:53.779075+00:00
-- url     : https://prove2.me/theorems/58a5b43e-c242-4cfa-8f89-5dc7c824d8fb
-- title:
--   Theorem B.1 (companion theorem; not used in the proof of the goal) — Tight single-agent transparency and zero-baseline optimality
-- statement:
--   For every single-agent finite-state contract setting, arbitrary prior and nonnegative cost,
--   $$U_P^F(D)\ge\frac89\mathrm{OPT}(D).$$
--   The nine-eighths loss is tight: for every $1\le\beta<9/8$ some single-agent instance has $U_P^F(D)>0$ and $\mathrm{OPT}(D)>\beta U_P^F(D)$. Finally,
--   $$\bigl[\forall\omega,\ f_\omega(\varnothing)=0\bigr]\ \Longrightarrow\ U_P^F(D)=\mathrm{OPT}(D).$$
--   All three clauses form one item. The universal inequality includes zero cost, costs at least one, positive baselines, zero baselines and zero-payoff cases. Positivity of a denominator is imposed only on the sharpness witnesses, never on the universal guarantee.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: 9/8 approximation, tightness and exact optimality when p0=0 in every state → the multiplied 8/9 inequality, a positive-payoff counterexample to every better factor, and equality of full and optimal information under zero baseline; reason: multiplication preserves the zero-payoff cases; quantified sharpness expresses the limiting worst case without asserting attainment at positive cost
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Theorem B.1, printed p. 25 (PDF p. 27)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Information

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Theorem B.1, printed 25 / PDF 27: universal bound, sharpness, and the
zero-baseline optimality clause, with no positivity assumption on general costs. -/
theorem theorem_B_1 :
    (∀ (m : ℕ) (M : Model 1 m) (D : Belief m),
      (8 / 9 : ℝ) * optimalInformation M D ≤ fullInformation M D) ∧
    (∀ β : ℝ, 1 ≤ β → β < (9 / 8 : ℝ) →
      ∃ (m : ℕ) (M : Model 1 m) (D : Belief m),
        0 < fullInformation M D ∧ β * fullInformation M D < optimalInformation M D) ∧
    (∀ (m : ℕ) (M : Model 1 m) (D : Belief m),
      (∀ ω, M.f ω ∅ = 0) → fullInformation M D = optimalInformation M D) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
