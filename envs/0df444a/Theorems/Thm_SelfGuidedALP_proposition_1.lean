-- Prove2me | Theorems.Thm_SelfGuidedALP_proposition_1
-- name    : SelfGuidedALP.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:29:17.332707+00:00
-- url     : https://prove2.me/theorems/a7af4ae6-d477-4050-91a6-2016ed701b66
-- title:
--   Proposition 1, p.9 — an optimal FELP solution represents $V^*$
-- statement:
--   Suppose $V^*\in\mathcal R$. Then there is an optimal FELP solution $\boldsymbol\beta^*=(\beta_0^*,B^*)$ such that
--   $$
--   V^*(s)=\beta_0^*+\int_\Theta B^*(\theta)\,\varphi(s;\theta)\,\mathrm d\theta\qquad\text{for all }s\in\mathcal S .
--   $$
--   Here $\nu$ is any state-relevance distribution.
--
--   This identifies the feature-based exact linear program with the value function, and it is what lets the paper speak of the weighting function $B^*$ of $V^*$.
--
--   Differences from the source:
--   - encoding: V* := PC(·,π*) for an optimal stationary policy (Assumption 1, p.7) → V is continuous on S and solves the Bellman optimality equation with the minimum attained; reason: the paper uses V* only through this equation (p.8, p.ec2); with γ < 1 its continuous solution is unique, and it is the optimal value under Assumption EC.1
--   - generalization: Assumption EC.1 and the existence of π* (pp.7, ec1) → dropped: no boundedness, semicontinuity or kernel continuity is assumed; reason: those conditions only guarantee that V* exists and solves the Bellman equation, which is now a hypothesis; a paper instance satisfies the Lean hypotheses
--   - encoding: each action set is continuous compact or finite → each A s is a nonempty compact subset of ℝᵐ; reason: a finite set is compact, so both cases are covered
--   - reading: Assumption 2 not repeated in the statement → Assumption 2 is a hypothesis; reason: p.ec1: Assumptions 1 and 2 hold for all proofs in the electronic companion
--   - encoding: the constraint ‖B/ρ‖_{2,ρ} < ∞ → B is an element of ℬ; reason: finiteness of the printed integral and of its square root are the same condition
--   - reading: integrals dθ with a sampling density ρ(θ) on Θ ⊆ ℝ^{d+1} → dθ is Lebesgue measure on ℝ^{d+1} and ρ a density for it; reason: the paper never names another reference measure, and its Definition EC.2 calls ℬ an L² space; laws without a Lebesgue density (Table 1's sphere and stump, p.8) are outside this reading
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Proposition 1, p.9

import Mathlib
import Definitions.Def_SelfGuidedALP_Assumption2
import Definitions.Def_SelfGuidedALP_IsOptimalValue
import Definitions.Def_SelfGuidedALP_IsFELPOptimal
import Definitions.Def_SelfGuidedALP_IsStateRelevance

open MeasureTheory

namespace SelfGuidedALP

/-- Proposition 1 of Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.9: if `V* ∈ ℛ`, there is an optimal FELP solution representing `V*`.
Assumption 2 holds for all proofs in the e-companion (p.ec1); it contains `V* ∈ ℛ`. -/
theorem proposition_1 {d m : ℕ} (M : MDP d m) (R : RBClass d) (L : ℝ)
    (Vstar : EuclideanSpace ℝ (Fin d) → ℝ) (hVstar : IsOptimalValue M Vstar)
    (hA2 : Assumption2 M R L Vstar) (ν : Measure (EuclideanSpace ℝ (Fin d))) (hν : IsStateRelevance M ν) :
    ∃ (βs : ℝ) (Bs : Bspace R), IsFELPOptimal M R ν βs Bs ∧ IsRep M R Vstar βs Bs := by sorry

end SelfGuidedALP
