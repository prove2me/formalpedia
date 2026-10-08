-- Prove2me | Theorems.Thm_ReliableFacilityLoc_RRSP_proposition4_lower_bound
-- name    : ReliableFacilityLoc.RRSP.proposition4_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:55.772176+00:00
-- url     : https://prove2.me/theorems/20b70a80-df57-4127-b504-3aee387ba056
-- title:
--   Proposition 4: the fixed-probability reformulation (RRSP$_i$) lower-bounds the relaxed subproblem (RSP$_i$)
-- statement:
--   Fix one customer $i$ with demand rate $\lambda_i \ge 0$, unit costs $d_{ij}$ ($j = 0,\dots,J-1$), penalty $\varphi_i = d_{iJ}$, failure probabilities $0 \le q_j < 1$, Lagrange multipliers $\mu_{ij} \ge 0$, and $R \ge 1$. Let $j_0, \dots, j_{J-1}$ order the regular facilities so that $q_{j_0} \le \dots \le q_{j_{J-1}}$, and define $\alpha_r$, $\beta_r$ from this ordering. Then for every feasible solution $(Y, P, W)$ of the relaxed subproblem (RSP$_i$) there is a feasible solution $Y'$ of the reformulation (RRSP$_i$) with
--
--   $$
--   \sum_{j=0}^{J-1}\sum_{r=0}^{R-1} \big(\lambda_i d_{ij}\alpha_r + \mu_{ij}\big) Y'_{jr} + \sum_{r=0}^{R} \lambda_i d_{iJ} \beta_r Y'_{Jr}
--   \;\le\; \sum_{j=0}^{J}\sum_{r=0}^{R} \lambda_i d_{ij} W_{jr} + \sum_{j=0}^{J-1}\sum_{r=0}^{R-1} \mu_{ij} Y_{jr}.
--   $$
--
--   Since both problems have finitely many feasible solutions, this says $\min(\text{RRSP}_i) \le \min(\text{RSP}_i)$: the assignment problem (RRSP$_i$), solvable in strongly polynomial time, gives a lower bound for the subproblem of the Lagrangian relaxation.
--
--   **Formalization Note** The hypothesis $\mu_{ij} \ge 0$ is not printed in the proposition. The $\mu_{ij}$ are the multipliers of the $\le$-constraints (1c) of a minimization, which are nonnegative in the subgradient method of §3.2; without the sign the statement is false (for instance $J = 2$, $R = 1$, $d = (3.09, 4.73)$, $q = (0.62, 0.86)$, $\varphi_i = -0.93$, $\mu = (2.18, -2.99)$, $\lambda_i = 2.3$: $\min(\text{RSP}_i) = -3.306$ but $\min(\text{RRSP}_i) = -2.139$). "Yields a lower bound" is stated in the for-all/exists form above, which avoids taking an infimum. The ordering is any bijection $\sigma$ with $q\circ\sigma$ nondecreasing; ties are broken arbitrarily. Constraints (4b) and (7b) are corrected to sum over all facilities $j = 0, \dots, J$. No sign is assumed on $d_{ij}$ or $\varphi_i$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 14 (PDF 16), Proposition 4; proof in Appendix A.4, pp. 37–39 (PDF 39–41)

import Mathlib
import Definitions.Def_ReliableFacilityLoc_RRSP_RSP
import Definitions.Def_ReliableFacilityLoc_RRSP_RRSP

open Finset

namespace ReliableFacilityLoc.RRSP

/-- **Proposition 4** (Cui, Ouyang & Shen, UCTC-FR-2010-02 (Feb. 2010), §3.3.2, p. 14, PDF 16;
proof in Appendix A.4, pp. 37–39, PDF 39–41). Fix one customer `i` with demand rate `λ_i ≥ 0`,
unit costs `d_ij`, penalty `φ_i`, failure probabilities `0 ≤ q_j < 1`, Lagrange multipliers
`µ_ij ≥ 0`, and `R ≥ 1`, and let `σ` order the regular facilities by nondecreasing failure
probability. For every feasible solution `(Y, P, W)` of the relaxed subproblem (RSP_i) (4a)–(4h)
there is a feasible solution `Y'` of (RRSP_i) (7a)–(7e) whose (RRSP_i) objective is at most the
(RSP_i) objective of `(Y, P, W)`. Equivalently (both feasible sets are finite and nonempty),
`min (RRSP_i) ≤ min (RSP_i)`.

Printed: "Proposition 4. The (RRSP) formulation (7a)-(7e) yields a lower bound to the relaxed
subproblem (4a)-(4h)."

Formalization Note:
1. `µ_ij ≥ 0` is not printed in the proposition. The `µ_ij` are the Lagrange multipliers of the
   `≤`-constraints (1c) of a minimization (§3.2, p. 12), which are nonnegative in the standard
   subgradient method the paper uses; without this sign the proposition is false (J = 2, R = 1,
   d = (3.09, 4.73), q = (0.62, 0.86), φ = −0.93, µ = (2.18, −2.99), λ = 2.3: min (RSP) = −3.306,
   min (RRSP) = −2.139).
2. (4b) and (7b) are corrected to sum over all facilities `j = 0, …, J` (see `IsLevelAssignment`).
3. "yields a lower bound" is stated in the `∀ ∃` form, which avoids taking an infimum.
4. The ordering `σ` is any bijection with `q ∘ σ` monotone; ties are broken arbitrarily.
5. `λ_i ≥ 0`, `0 ≤ q_j < 1`, `R ≥ 1` are the standing assumptions of §3.1 (p. 8). No sign is
   assumed on `d_ij` or `φ_i`. -/
theorem proposition4_lower_bound {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1)
    (hmu : ∀ j, 0 ≤ mu j) (hR : 1 ≤ R) (σ : Fin J ≃ Fin J) (hσ : IsQOrdering q σ)
    (Y P W : Fin (J + 1) → Fin (R + 1) → ℝ) (h : IsRSPFeasible q Y P W) :
    ∃ Y' : Fin (J + 1) → Fin (R + 1) → ℝ, IsLevelAssignment Y' ∧
      rrspObjective lam d phi q mu σ Y' ≤ rspObjective lam d phi mu Y W := by sorry

end ReliableFacilityLoc.RRSP
