-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Scenario_ssp_to_rufl
-- name    : ReliableFacilityLoc.Scenario.ssp_to_rufl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:57.797636+00:00
-- url     : https://prove2.me/theorems/73ddc5e2-c5ce-4133-8b52-a9e6880cece1
-- title:
--   With $R = J$, a nearest-server (SSP) solution has a (RUFL)-feasible counterpart of equal cost
-- statement:
--   Suppose $R = J$. Let $(X,Y)$ be a feasible solution of (SSP) in which every customer in every scenario is served by her nearest operating open facility (ties to the lowest index, with $\delta_{J\omega} = 1$ and $X_J = 1$). Then there are $Y'$, $P'$ such that $(X,Y',P')$ is feasible for (RUFL) and
--   $$\Phi(X,Y',P') = \Psi(X,Y).$$
--   The paper's $Y'$ assigns customer $i$, in nondecreasing order of distance (ties to the lower index), to the open sites $j$ with $d_{ij} \le d_{iJ}$, followed by the emergency facility $J$; and $P'$ is the corresponding level probability $(1-q_{j(i,r)})\prod_{\ell<r} q_{j(i,\ell)}$.
--
--   Consequently the optimal value of (RUFL) is at most that of (SSP): "the optimal solution to (SSP) is also a lower bound to (RUFL)".
--
--   **Formalization Note** The paper applies the construction to an optimal, normalized solution of (SSP); it uses only feasibility and the normalization, so the statement is made for every such solution. $R = J$ is built into the type of the instance; it is what allows all open sites to be placed on the levels $0,\dots,R-1$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), Appendix A.1 (proof of Proposition 1), pp. 33–34 (PDF 35–36), construction of (X′, Y′, P′) and the display ending "= Ψ(X, Y)"

import Definitions.Def_ReliableFacilityLoc_Scenario_RUFL
import Definitions.Def_ReliableFacilityLoc_Scenario_SSP

open Finset

namespace ReliableFacilityLoc.Scenario

/-- **(SSP) → (RUFL) with equal cost when `R = J`** (Cui–Ouyang–Shen, UCTC-FR-2010-02 (Feb. 2010),
A.1, proof of Proposition 1, pp. 33–34 (PDF 35–36)). Let `R = J`. For every (SSP)-feasible
`(X, Y)` in the normalized form of p. 33 (each customer in each scenario served by her closest
operating open facility, ties to the lowest index) there is a (RUFL)-feasible `(X', Y', P')` with
`X' = X` and `Φ(X', Y', P') = Ψ(X, Y)`; hence the optimal value of (RUFL) is at most that of (SSP)
("the optimal solution to (SSP) is also a lower bound to (RUFL)").

Formalization Note: the paper starts from an optimal `(X, Y)` normalized as on p. 33; its
construction (levels = the open facilities `j` with `d_ij ≤ d_iJ` in nondecreasing distance, ties
to the lower index, followed by `J`) uses only feasibility and the normalization, so the statement
is made for every such feasible solution. `R = J` is the instance type `Instance I J J`; it is what
lets all open facilities fit on the levels `0, …, R-1`. -/
theorem ssp_to_rufl {I J : ℕ} (D : Instance I J J) (X : Fin J → ℝ)
    (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ) (h : D.IsSSPFeasible X Y)
    (hY : ∀ i ω k, Y i k ω = 1 ↔ D.IsNearestServer X i ω k) :
    ∃ Y' P' : Fin I → Fin (J + 1) → Fin (J + 1) → ℝ,
      D.IsRUFLFeasible X Y' P' ∧ D.ruflObjective X Y' P' = D.sspObjective X Y := by sorry

end ReliableFacilityLoc.Scenario
