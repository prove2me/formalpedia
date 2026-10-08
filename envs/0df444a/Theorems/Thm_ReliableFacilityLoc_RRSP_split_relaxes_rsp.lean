-- Prove2me | Theorems.Thm_ReliableFacilityLoc_RRSP_split_relaxes_rsp
-- name    : ReliableFacilityLoc.RRSP.split_relaxes_rsp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:01.963095+00:00
-- url     : https://prove2.me/theorems/c20eedc1-1e67-4aa9-9e19-76353c0999c2
-- title:
--   The split formulation (19a)–(19l) is a relaxation of (RSP$_i$)
-- statement:
--   Let $(Y, P, W)$ be feasible for the relaxed subproblem (RSP$_i$). Then $(Y, Z, P, W)$ with $Z = Y$ is feasible for the split formulation (19a)–(19l), and its cost equals the (RSP$_i$) objective:
--
--   $$
--   G(Y, Y, P) = \sum_{j=0}^{J}\sum_{r=0}^{R} \lambda_i d_{ij} W_{jr} + \sum_{j=0}^{J-1}\sum_{r=0}^{R-1} \mu_{ij} Y_{jr}.
--   $$
--
--   Hence the optimal value of the split formulation is at most the optimal value of (RSP$_i$). This is the last step of the proof of Proposition 4.
--
--   **Formalization Note** No assumption on the data is needed. Feasibility and cost are those of the RSP and split-formulation definitions.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 39 (PDF 41), Appendix A.4, last paragraph of the proof of Proposition 4 (unnumbered)

import Mathlib
import Definitions.Def_ReliableFacilityLoc_RRSP_RSP
import Definitions.Def_ReliableFacilityLoc_RRSP_Split

open Finset

namespace ReliableFacilityLoc.RRSP

/-- **The split formulation (19a)–(19l) is a relaxation of (RSP_i)** (Cui, Ouyang & Shen,
UCTC-FR-2010-02 (Feb. 2010), Appendix A.4, p. 39, PDF 41, last paragraph; unnumbered). Every
feasible solution `(Y, P, W)` of (RSP_i) gives the feasible solution `(Y, Z, P, W)` with `Z = Y` of
the split formulation (this is constraint (19m)), with the same cost: `G(Y, Y, P) = Φ_i`.

Printed: "Since formulation (19a) - (19l) is a relaxation of (RSP), it follows that (RRSP) yields a
lower bound for (RSP)."

Formalization Note: the split formulation is the one of `IsSplitFeasible` / `splitObjective`
(with the objective the proof of Lemma 1 uses, see there). No hypothesis on the data is needed. -/
theorem split_relaxes_rsp {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (Y P W : Fin (J + 1) → Fin (R + 1) → ℝ) (h : IsRSPFeasible q Y P W) :
    IsSplitFeasible q Y Y P W ∧
      splitObjective lam d phi mu Y W = rspObjective lam d phi mu Y W := by sorry

end ReliableFacilityLoc.RRSP
