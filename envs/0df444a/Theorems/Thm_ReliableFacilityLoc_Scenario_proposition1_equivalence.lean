-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Scenario_proposition1_equivalence
-- name    : ReliableFacilityLoc.Scenario.proposition1_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:09.493003+00:00
-- url     : https://prove2.me/theorems/dd66aeb8-f836-4fc2-940e-a25b34bb097c
-- title:
--   Proposition 1 — with $R = J$, (RUFL) and the scenario-based program (SSP) have the same optimal value
-- statement:
--   **Proposition 1** (Cui, Ouyang and Shen). If $R = J$, then the compact formulation (RUFL) (1a)–(1g) is equivalent to the stochastic programming formulation (SSP) (17a)–(17d) that covers all $2^J$ failure scenarios.
--
--   Precisely: let the data be customers $i$ with demand rates $\lambda_i \ge 0$, regular sites $j = 0,\dots,J-1$ with fixed costs $f_j$ and independent failure probabilities $0 \le q_j < 1$, unit costs $d_{ij}$, penalties $\phi_i$ (the costs $d_{iJ}$ of the never-failing emergency facility $J$), and $R = J \ge 1$ assignment levels beyond level $0$. Then
--   1. (RUFL) has an optimal solution;
--   2. (SSP) has an optimal solution;
--   3. for every optimal solution $(X,Y,P)$ of (RUFL) and every optimal solution $(X',Y')$ of (SSP),
--   $$\Phi(X,Y,P) = \Psi(X',Y').$$
--
--   The proposition justifies replacing an exponentially large scenario-based stochastic program by a compact, polynomial-size mixed-integer program when each customer may be assigned to as many backup facilities as there are sites.
--
--   **Formalization Note** "Equivalent" is read, as in the paper's proof, as equality of optimal values; existence of optima is stated so that the equality is not vacuous. $R = J$ is built into the type of the instance, and $R \ge 1$ (p. 8) then means $J \ge 1$. Both formulations use the corrected constraints: the first sum of (1b) runs over all $J+1$ facilities, and (17c) is imposed per customer.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 10 (PDF 12), Proposition 1; proof in Appendix A.1, pp. 32–34 (PDF 34–36); (1b) and (17c) corrected

import Definitions.Def_ReliableFacilityLoc_Scenario_RUFL
import Definitions.Def_ReliableFacilityLoc_Scenario_SSP

open Finset

namespace ReliableFacilityLoc.Scenario

/-- **Proposition 1** (Cui–Ouyang–Shen, UCTC-FR-2010-02 (Feb. 2010), p. 10 (PDF 12); proof in
A.1, pp. 32–34 (PDF 34–36)): "If `R = J`, then formulation (1a)-(1g) is equivalent to the
stochastic programming formulation that covers all failure scenarios." Both (RUFL) (1a)–(1g) and
the scenario-based program (SSP) (17a)–(17d) have optimal solutions, and every optimal solution
of (RUFL) has the same objective value as every optimal solution of (SSP).

Formalization Note: "equivalent" is read, as in the proof, as equality of optimal values; the
existence of optima is stated so that the equality is not vacuous. `R = J` is the instance type
`Instance I J J`; with the standing assumption `R ≥ 1` (p. 8) this means `J ≥ 1`. Both
formulations use the corrected constraints (1b) and (17c) (see `IsRUFLFeasible`, `IsSSPFeasible`):
the first sum of (1b) runs over all `J + 1` facilities, and (17c) is imposed per customer. -/
theorem proposition1_equivalence {I J : ℕ} (D : Instance I J J) :
    (∃ (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (J + 1) → ℝ), D.IsRUFLOptimal X Y P) ∧
    (∃ (X : Fin J → ℝ) (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ), D.IsSSPOptimal X Y) ∧
    ∀ (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (J + 1) → ℝ) (X' : Fin J → ℝ)
      (Y' : Fin I → Fin (J + 1) → FailureScenario J → ℝ),
      D.IsRUFLOptimal X Y P → D.IsSSPOptimal X' Y' →
        D.ruflObjective X Y P = D.sspObjective X' Y' := by sorry

end ReliableFacilityLoc.Scenario
