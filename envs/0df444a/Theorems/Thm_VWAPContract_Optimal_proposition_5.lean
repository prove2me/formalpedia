-- Prove2me | Theorems.Thm_VWAPContract_Optimal_proposition_5
-- name    : VWAPContract.Optimal.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:14.6737+00:00
-- url     : https://prove2.me/theorems/e84c3245-4377-4448-a894-10d1aec2bacc
-- title:
--   Proposition 5, p. 22 (PDF 23) — in the specialized model, the guaranteed VWAP contract $\tau^{VWAP}$ is optimal
-- statement:
--   In the specialized client–dealer execution model, the guaranteed VWAP contract
--
--   $$\tau^{\mathrm{VWAP}}(p,v)=\frac{\sum_{t=1}^T p_tv_t}{\sum_{s=1}^T v_s}$$
--
--   is optimal for the client: it belongs to a feasible contract–static-policy pair whose expected payment is no greater than that of every feasible measurable contract and static policy. Feasibility includes individual rationality, incentive compatibility, and finite expected payment, cost, and dealer utility.
--
--   The proposition establishes the paper's main optimality assertion across the full contract class, with the paper's arbitrary admissible impact, volume, utility, and shock distributions.
--
--   **Formalization Note** The model explicitly requires measurable functions, integrable shocks and first-best impact cost, positive market conditions, and $T\ge1$. Incentive compatibility ranges over integrable-utility static deviations, which retains all deviations relevant under VWAP.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), p. 22 (PDF 23), Proposition 5

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem proposition_5 {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (hM : M.Standing) :
    IsOptimal M tauVWAP := by sorry

end VWAPContract.Optimal
