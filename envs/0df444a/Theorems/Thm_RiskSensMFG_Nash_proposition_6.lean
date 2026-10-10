-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_proposition_6
-- name    : RiskSensMFG.Nash.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:42.968834+00:00
-- url     : https://prove2.me/theorems/e820b2f3-0a74-41f4-b20e-930b58db5d31
-- title:
--   Proposition 6, p. 26 — the augmented model has the same finite-horizon risk-sensitive costs as the original one
-- statement:
--   Assume the standing assumptions and Assumptions 1 and 2-(a), and fix a horizon $n$.
--
--   1. For every $N\ge1$, every profile $\boldsymbol\pi^{(N)}$ of Markov policies and every agent $i$,
--   $$\hat J^{(N),n}_i(\boldsymbol\pi^{(N)})=J^{(N),n}_i(\boldsymbol\pi^{(N)}).$$
--   2. For every Markov policy $\pi$ and every flow $\boldsymbol\Delta=(\Delta_t)_{t\ge0}\subset\mathcal P(\mathsf S)$,
--   $$\hat J^n_{\boldsymbol\Delta}(\pi)=J^n_{\boldsymbol\mu}(\pi),\qquad \boldsymbol\mu=(\Delta_{t,1})_{t\ge0}.$$
--
--   The proposition lets the rest of the proof work in the augmented model, where the cost is a terminal cost.
--
--   **Formalization Note** The terminal cost is the clamped $e^{\lambda\max(0,\min(c,L))}$ of the augmented model; the identity uses $0\le c\le K$ (standing assumptions and Assumption 1-(a)), which keeps the accumulated cost in $[0,L]$.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 26, Proposition 6; proof Appendix A, pp. 31–32

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game
import Definitions.Def_RiskSensMFG_Nash_Augmented

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace RiskSensMFG.Nash

theorem proposition_6 {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (h2a : Assumption2a M) (n : ℕ) :
    (∀ (N : ℕ), 1 ≤ N → ∀ (πs : Fin N → MarkovPolicy X A) (i : Fin N),
      JhatN M hS.measurable_c N πs i n = JNfin M N πs i n) ∧
    (∀ (σ : MarkovPolicy X A) (Δ : ℕ → RiskSensMFG.Existence.PM (X × ℝ)),
      Jhat M hS.measurable_c Δ σ n = Jfin M (fun t => marg (Δ t)) σ.toPolicy n) := by sorry

end RiskSensMFG.Nash
