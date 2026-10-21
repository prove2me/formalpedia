-- Prove2me | Theorems.Thm_PharmaEPR_Welfare_proposition_1
-- name    : PharmaEPR.Welfare.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:35.832663+00:00
-- url     : https://prove2.me/theorems/a3af2a3f-922b-4b42-b0b2-21a747f39ca9
-- title:
--   Proposition 1, p. 15 — health-benefit thresholds for profitable over-prescription
-- statement:
--   Suppose the model's standing regime holds and $\alpha+\beta<1$. The health-benefit thresholds satisfy $\bar u_p^{EC}<\bar u_p^{SR}$. Below the EC threshold, every collection rate in $[0,1]$ at which an optimal producer action has nonnegative profit admits an over-prescribing feasible action whose profit strictly exceeds that of every feasible no-over-prescribing action. Below the SR threshold, the analogous claim holds for every nonnegative fee at which an optimal producer action has nonnegative profit.
--
--   $$u_p<\bar u_p^P\quad\Longrightarrow\quad
--   \Pi_m^P(\text{some over-prescribing action})>
--   \Pi_m^P(\text{every no-over-prescribing action}),\qquad P\in\{EC,SR\}.$$
--
--   The result identifies when neither policy can make avoiding over-prescription privately optimal for the producer while retaining producer participation.
--
--   **Formalization Note** The strict threshold ordering requires $\alpha+\beta<1$; the appendix proves only a weak ordering at equality. Under the goal's nonnegative $u_p$ and $\alpha<1/4$, the EC premise $u_p<\bar u_p^{EC}$ cannot occur, but the SR premise can.
-- source:
--   Alev, Atasu, Toktay & Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020-09-05 posting), p. 15, Proposition 1; proof Online Appendix pp. 1–2

import Mathlib
import Definitions.Def_PharmaEPR_Welfare_Model

namespace PharmaEPR.Welfare

theorem proposition_1 (P : Params) (hP : Regime P)
    (hstrict : P.alpha + P.beta < 1) :
    (P.up < uEC P → ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 →
      (∃ a, ProdOptimal P .EC ⟨r, 0⟩ a ∧
        0 ≤ prodProfit P .EC ⟨r, 0⟩ a) →
      ∃ a, ProdFeasible P a ∧ OverPrescribes P a ∧
        ∀ a', ProdFeasible P a' → ¬ OverPrescribes P a' →
          prodProfit P .EC ⟨r, 0⟩ a' < prodProfit P .EC ⟨r, 0⟩ a) ∧
    (P.up < uSR P → ∀ t : ℝ, 0 ≤ t →
      (∃ a, ProdOptimal P .SR ⟨0, t⟩ a ∧
        0 ≤ prodProfit P .SR ⟨0, t⟩ a) →
      ∃ a, ProdFeasible P a ∧ OverPrescribes P a ∧
        ∀ a', ProdFeasible P a' → ¬ OverPrescribes P a' →
          prodProfit P .SR ⟨0, t⟩ a' < prodProfit P .SR ⟨0, t⟩ a) ∧
    uEC P < uSR P := by sorry

end PharmaEPR.Welfare
