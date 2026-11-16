-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_theorem_5_1
-- name    : TransparencyTeamContracts.Submodular.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:18:59.122525+00:00
-- url     : https://prove2.me/theorems/1b900e73-53b9-470e-88cb-b43338311a4c
-- title:
--   Theorem 5.1 (companion theorem; not used in the proof of the goal) — Unbounded loss with supermodular rewards
-- statement:
--   There exists an instance with exactly two agents, two equally likely states and supermodular state technologies such that
--   $$U_P^F(D)=0,\qquad U_P^N(D)>0.$$
--   The complete normalized witness is retained: costs are $(1/4,1/2)$, and the technology values on $(\varnothing,\{0\},\{1\},\{0,1\})$ are $(0,1/4,1/4,1)$ in state 0 and $(0,5/42,0,5/6)$ in state 1. The contract $(6/19,28/41)$ is feasible, makes both agents working a pure equilibrium before disclosure, and pays the principal exactly $11/9348>0$.
--
--   The full-information equality concerns the optimum over all contracts and equilibria, rather than a selected contract giving zero. The model fields are fixed to the displayed data, so the existential model certifies their validity as a contract instance.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: the two-agent/two-state proof witness, with every reward and cost divided by 8 → the normalized reward tables, costs, uniform prior and exact positive utility 11/9348 are explicit in the existential conclusion; reason: the paper instructs this normalization; incentives are unchanged and all principal utilities are divided by 8; zero-based labels merely relabel the two agents
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Theorem 5.1, printed p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_Mixed
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_SingleAgent

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Theorem 5.1, printed 18 / PDF 20, including the printed normalized witness.
Equalities to the raw data fix the entire model, not just a candidate contract. -/
theorem theorem_5_1 :
    ∃ (M : Model 2 2) (D : Belief 2), M.f = complementReward ∧ M.c = complementCost ∧
      (∀ ω, (D : Fin 2 → ℝ) ω = 1 / 2) ∧
      (∀ ω, IsSupermodular (M.f ω)) ∧
      fullInformation M D = 0 ∧ 0 < noInformation M D ∧
      IsContract complementContract ∧
      IsEquilibrium (posteriorReward M D) M.c complementContract univ ∧
      principalUtility (posteriorReward M D) complementContract univ = 11 / 9348 := by sorry

end TransparencyTeamContracts.Submodular.Supplement
