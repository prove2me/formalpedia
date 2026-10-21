-- Prove2me | Theorems.Thm_TeamDelegation_Optimal_proposition_7
-- name    : TeamDelegation.Optimal.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:24.371394+00:00
-- url     : https://prove2.me/theorems/c30580e0-3357-4446-afb4-382288e4daed
-- title:
--   Proposition 7: strictly cheaper collusion-proof delegation exists
-- statement:
--   For every production environment satisfying the standing assumptions and Assumption 1, and every pair of baseline adoption costs, there are cost differences $\Delta_A,\Delta_B$ with $\widehat\Delta_A<\Delta_A<\Delta_A^{\max}$ and $\Delta_B<\Delta_B^{\max}$ such that the paper's delegated bonuses implement both agents working with the correct method. Centralisation also implements that outcome at the equal bonus $w^{\mathrm{cent}}$, while delegation is strictly cheaper than **every** centralised success-bonus scheme that implements it:
--
--   $$\exists\Delta_A,\Delta_B:\quad
--   \operatorname{Implements}_{\mathrm{del}}(w_A^{\mathrm{del}},w_B^{\mathrm{del}}),\quad
--   \forall(w_A,w_B)\in\operatorname{Implements}_{\mathrm{cent}},\quad
--   p_2(w_A^{\mathrm{del}}+w_B^{\mathrm{del}})<p_2(w_A+w_B).$$
--
--   The resulting delegated desired path is collusion-proof. This establishes a nonempty region in which assigning the production-method choice to A reduces the principal's wage cost even after collusion is excluded.
--
--   **Formalization Note** Implementation uses the paper's grim-trigger one-shot-deviation characterisation with mixed Nash punishments. Collusion-proofness is strengthened from footnote 30 to exclude any Pareto-improving feasible state-dependent outcome lottery. The formal standing assumptions spell out $0\le r<1$ and the success-probability endpoints; the centralised implementation conjunct prevents a vacuous cost comparison.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 29 (PDF 30), Proposition 7

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

namespace TeamDelegation.Optimal

/-- Proposition 7, p. 29: a nonempty region of cost differences makes
delegation strictly cheaper than every implementing centralised wage scheme, while
the desired delegated path also resists Pareto-improving collusion. -/
theorem proposition_7 (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (c1A c1B : ℝ) :
    ∃ ΔA ΔB : ℝ,
      DeltaHatA P < ΔA ∧ ΔA < DeltaMaxA P ∧ ΔB < DeltaMaxB P ∧
      Implements P (Costs.ofDeltas c1A c1B ΔA ΔB) .deleg
        (wdelA P ΔA) (wdelB P ΔB) ∧
      Implements P (Costs.ofDeltas c1A c1B ΔA ΔB) .cent
        (wcent P) (wcent P) ∧
      (∀ wA wB : ℝ,
        Implements P (Costs.ofDeltas c1A c1B ΔA ΔB) .cent wA wB →
          wageCost P (wdelA P ΔA) (wdelB P ΔB) < wageCost P wA wB) ∧
      CollusionProof P (Costs.ofDeltas c1A c1B ΔA ΔB) .deleg
        (wdelA P ΔA) (wdelB P ΔB) := by sorry

end TeamDelegation.Optimal
