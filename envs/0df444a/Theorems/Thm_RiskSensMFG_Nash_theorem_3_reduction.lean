-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_theorem_3_reduction
-- name    : RiskSensMFG.Nash.theorem_3_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:37.218196+00:00
-- url     : https://prove2.me/theorems/f0dab59a-adce-466b-bc97-37c373745956
-- title:
--   Proof of Theorem 3, p. 30, first display — the best response among Markov policies can be approximated by weakly continuous ones
-- statement:
--   Assume the standing assumptions and Assumption 1. For every $N$, every profile $\boldsymbol\pi^{(N)}$ of Markov policies and every agent $i$,
--   $$\inf_{\pi^i\in\mathsf M_i}J^{(N)}_i(\boldsymbol\pi^{(N)}_{-i},\pi^i)=\inf_{\pi^i\in\mathsf M^c_i}J^{(N)}_i(\boldsymbol\pi^{(N)}_{-i},\pi^i),$$
--   where $\mathsf M^c_i$ is the set of weakly continuous Markov policies. Equivalently: for every Markov policy $\sigma$ and every $\delta>0$ there is a weakly continuous Markov policy $\sigma'$ with
--   $$J^{(N)}_i(\boldsymbol\pi^{(N)}_{-i},\sigma')\le J^{(N)}_i(\boldsymbol\pi^{(N)}_{-i},\sigma)+\delta .$$
--
--   This reduces the $\varepsilon$-Nash property to deviations by weakly continuous policies, to which Theorem 4 and Corollary 1 apply.
--
--   **Formalization Note** The Lean statement is the second (approximation) form; the inequality "$\le$" between the infima holds since $\mathsf M^c_i\subseteq\mathsf M_i$. The paper refers the proof to [38, Theorem 2.3]; Assumption 2 is not assumed.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 30, proof of Theorem 3, first display (referred to the proof of [38, Theorem 2.3])

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game

open MeasureTheory ProbabilityTheory Filter Topology

namespace RiskSensMFG.Nash

theorem theorem_3_reduction {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M)
    (N : ℕ) (πs : Fin N → MarkovPolicy X A) (i : Fin N) (σ : MarkovPolicy X A)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ σ' : MarkovPolicy X A, σ'.WeaklyContinuous ∧
      JN M N (Function.update πs i σ') i ≤ JN M N (Function.update πs i σ) i + δ := by sorry

end RiskSensMFG.Nash
