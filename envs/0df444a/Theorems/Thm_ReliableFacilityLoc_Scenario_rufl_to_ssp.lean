-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Scenario_rufl_to_ssp
-- name    : ReliableFacilityLoc.Scenario.rufl_to_ssp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:19.759978+00:00
-- url     : https://prove2.me/theorems/fffe6c04-d4c5-4bdd-8dda-96517d99958f
-- title:
--   Every (RUFL)-feasible solution has an (SSP)-feasible counterpart of equal cost
-- statement:
--   Let $(X,Y,P)$ be a feasible solution of (RUFL), with any number $R \ge 1$ of levels. Then there is an assignment $Y'$ such that $(X,Y')$ is feasible for the scenario-based program (SSP) and
--   $$\Psi(X,Y') = \Phi(X,Y,P).$$
--   The paper's $Y'$ serves customer $i$ in scenario $\omega$ by the first facility among her assigned levels that operates in $\omega$.
--
--   Consequently the optimal value of (SSP) is at most that of (RUFL): "solving (SSP) yields a lower bound to (RUFL)".
--
--   **Formalization Note** The paper applies the construction to an optimal solution of (RUFL), but it uses only feasibility, so the statement is made for every feasible solution. The location vector is kept unchanged ($X' = X$).
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), Appendix A.1 (proof of Proposition 1), pp. 32–33 (PDF 34–35), construction of (X′, Y′) and the display ending "= Φ(X, Y, P)"

import Definitions.Def_ReliableFacilityLoc_Scenario_RUFL
import Definitions.Def_ReliableFacilityLoc_Scenario_SSP

open Finset

namespace ReliableFacilityLoc.Scenario

/-- **(RUFL) → (SSP) with equal cost** (Cui–Ouyang–Shen, UCTC-FR-2010-02 (Feb. 2010), A.1, proof
of Proposition 1, p. 33 (PDF 35)). For every (RUFL)-feasible `(X, Y, P)` there is an
(SSP)-feasible `(X', Y')` with `X' = X` and `Ψ(X', Y') = Φ(X, Y, P)`; hence the optimal value of
(SSP) is a lower bound on that of (RUFL) ("solving (SSP) yields a lower bound to (RUFL)").

Formalization Note: the paper starts from an optimal `(X, Y, P)`, but its construction (serve
customer `i` in scenario `ω` by the first operating facility among her assigned levels) uses only
feasibility, so the statement is made for every feasible solution. It holds for every `R ≥ 1`;
`R = J` is not needed in this direction. `X' = X` is built in by reusing `X`. -/
theorem rufl_to_ssp {I J R : ℕ} (D : Instance I J R) (X : Fin J → ℝ)
    (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (h : D.IsRUFLFeasible X Y P) :
    ∃ Y' : Fin I → Fin (J + 1) → FailureScenario J → ℝ,
      D.IsSSPFeasible X Y' ∧ D.sspObjective X Y' = D.ruflObjective X Y P := by sorry

end ReliableFacilityLoc.Scenario
