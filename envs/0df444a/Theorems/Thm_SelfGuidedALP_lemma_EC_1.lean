-- Prove2me | Theorems.Thm_SelfGuidedALP_lemma_EC_1
-- name    : SelfGuidedALP.lemma_EC_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:24:12.765423+00:00
-- url     : https://prove2.me/theorems/879f8853-9d9f-40b4-9451-56ac78698133
-- title:
--   Lemma EC.1, p.ec2 — a continuous $V$ feasible to (2) satisfies $V\le V^*$
-- statement:
--   Let $V:\mathcal S\to\mathbb R$ be continuous and feasible to the constraints (2), that is, $V(s)-\gamma\,\mathbb E[V(s')\mid s,a]\le c(s,a)$ for all $s\in\mathcal S$, $a\in\mathcal A_s$. Then
--   $$
--   V(s)\le V^*(s)\qquad\text{for all }s\in\mathcal S.
--   $$
--
--   This is the lower-bound property of approximate linear programs: every VFA feasible to (8) lies below $V^*$.
--
--   Differences from the source:
--   - encoding: V* := PC(·,π*) for an optimal stationary policy (Assumption 1, p.7) → V is continuous on S and solves the Bellman optimality equation with the minimum attained; reason: the paper uses V* only through this equation (p.8, p.ec2); with γ < 1 its continuous solution is unique, and it is the optimal value under Assumption EC.1
--   - generalization: Assumptions 1, 2 and EC.1 in force (p.ec1) → only the MDP record and the Bellman hypothesis on V*; reason: the argument at a maximizer of V − V* uses nothing else; a paper instance satisfies the Lean hypotheses
--   - encoding: each action set is continuous compact or finite → each A s is a nonempty compact subset of ℝᵐ; reason: a finite set is compact, so both cases are covered
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Lemma EC.1, p.ec2

import Mathlib
import Definitions.Def_SelfGuidedALP_ELPFeasible
import Definitions.Def_SelfGuidedALP_IsOptimalValue

namespace SelfGuidedALP

/-- Lemma EC.1 of Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.ec2: any continuous function feasible to the constraints (2) is
below `V*` on `𝒮`. -/
theorem lemma_EC_1 {d m : ℕ} (M : MDP d m) (Vstar V : EuclideanSpace ℝ (Fin d) → ℝ)
    (hVstar : IsOptimalValue M Vstar) (hcont : ContinuousOn V M.S) (hfeas : ELPFeasible M V) :
    ∀ s ∈ M.S, V s ≤ Vstar s := by sorry

end SelfGuidedALP
