-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_theorem_4
-- name    : SuspensionContract.HighCostC2.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:11:48.466269+00:00
-- url     : https://prove2.me/theorems/71958f0e-40e9-48e8-9720-2f8bafb72da5
-- title:
--   Theorem 4 (corrected: published lower switching-cost threshold)
-- statement:
--   Under Condition 2 and the full interval $K\in[\underline K,\bar K_2)$, an optimal contract hires immediately and pays $\beta$ at each arrival in addition to reimbursing effort. Every realization of this always-work contract is optimal, with
--   $$U(\bar\Gamma)=\frac{(R-\beta)\mu-c}{r}-K.$$
--   The threshold $\underline K$ is the published source-supported correction of (33), not an assumed optimality threshold. Optimality compares against every feasible contract, rather than concluding only a QVI certificate.
--
--   Differences from the source:
--   - correction: D is called deterministic but only F-adaptedness is written. → The public filtration after initialization contains no noise beyond N and Q.; reason: Adaptedness alone admits an independent Poisson D and falsifies the two-noise PK equation; this implements the intended deterministic control. See DISPROOF.md.
--   - correction: The bracket in (33) contains (r/ρ)β. → The imported published Klow uses ((ρ−μ)/ρ)β.; reason: The proof identifies this threshold with (EC.69), giving the corrected term; the regime is not narrowed for proof convenience.
--   - encoding: Processes and equations are written without null-set conventions. → Utilities are actual conditional expectations; drift statements use predictable versions dt-a.e., jump statements use indistinguishable versions.; reason: This gives the standard stochastic interpretation and preserves all right-continuous binary deviations, both contract states and the infinite time horizon.
--   - generalization: Theorem 4 asserts optimality of the always-work contract. → Also states its value U(Γ̄)=((R−β)μ−c)/r−K for every realization.; reason: This is the closed form displayed on p.12 before (10); dropping the clause gives the printed theorem.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. 26, Theorem 4

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Regimes

namespace SuspensionContract.HighCostC2.Supplement

theorem theorem_4 (P : Params) (hP : P.Standing) (hC : P.Condition2)
    (hK : (toAW P).Klow ≤ P.K ∧ P.K < P.Kbar2) :
    (∃ G : Contract, IsAlwaysWork P G ∧ IsOptimal P G) ∧
    (∀ G : Contract, IsAlwaysWork P G → IsOptimal P G ∧
      principalUtility P G = (((P.R - P.β) * P.μ - P.c) / P.r - P.K : ℝ)) := by sorry

end SuspensionContract.HighCostC2.Supplement
