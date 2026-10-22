-- Prove2me | Theorems.Thm_SystemSqueeze_Accommodation_proposition_3
-- name    : SystemSqueeze.Accommodation.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:21.174987+00:00
-- url     : https://prove2.me/theorems/17c309d6-d5e1-4079-8730-6e6aa6a8d4ce
-- title:
--   Proposition 3, p. 19 — in the accommodation equilibrium, squeezing beats conversion iff U_I < U_C, and for large γ A enters with a loss-making integrated system
-- statement:
--   Let $U_C>0$ and $U_I>0$. In the accommodation equilibrium, for any $\gamma>0$ in the admissible range:
--
--   1. **(i), first sentence.** If $U_I<U_C$, then $A$'s incremental profit from squeezing exceeds its incremental profit from conversion: $\Delta\Pi_A^X>\Delta\Pi_A^Y$.
--   2. **(i), second sentence.** If $U_I<U_C$, there is a threshold $\hat\gamma<\bar\gamma(U_C,U_I)=(\sqrt{U_C^2+3U_I^2}-U_C)/U_I$ such that for every admissible $\gamma>\hat\gamma$ there is an entry cost $K\ge0$ at which the stage-1 outcome is accommodation ($A$ enters, $B$ does not) while $A$'s profit from selling the integrated system is negative:
--   $$P_{I_A}^{(ii)}Q_{I_A}^{(ii)}-K<0.$$
--   3. **(ii).** If $U_I>U_C$, then $\Delta\Pi_A^Y>\Delta\Pi_A^X$.
--
--   Here $\Delta\Pi_A^X$ and $\Delta\Pi_A^Y$ are computed from any Nash equilibrium price profiles of the no-entry and the accommodation subgames, and the accommodation outcome from any equilibrium profiles of all three subgames. The result explains why a complementor may launch an integrated system that loses money by itself: the entry squeezes the rival complementor's margin, and the gain on the entrant's own component pays for the loss.
--
--   **Formalization Note** "Sufficiently large" is an existential threshold $\hat\gamma$ that must lie strictly below the upper end of the admissible range, so the claim cannot hold vacuously. "A enters" is read as the stage-1 accommodation outcome (A enters given B stays out, and B stays out given A is in), not merely $A$'s entry benefit being nonnegative. The profit from selling the integrated system is taken net of the investment $K$, as in the proof (p. 37). The conclusions quantify over the equilibrium predicates; no closed-form price is substituted.
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), p. 19 (PDF 20), Proposition 3; proof pp. 36–37 (PDF 37–38)

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

namespace SystemSqueeze.Accommodation

/-- Proposition 3, p. 19. In the accommodation equilibrium, for any `γ > 0`:
(i) if `UI < UC`, `A`'s incremental profit from squeezing `ΔΠ_A^X` exceeds its incremental
profit from conversion `ΔΠ_A^Y`; and if `γ` is sufficiently large, `A` enters (the stage-1
outcome is accommodation at some entry cost `K ≥ 0`) even though its profit from selling the
integrated system, net of `K`, is negative;
(ii) if `UI > UC`, `ΔΠ_A^Y` exceeds `ΔΠ_A^X`.
"Sufficiently large" is a threshold `γ̂` strictly below the admissible bound `gammaMax UC UI`. -/
theorem proposition_3 (UC UI : ℝ) (hUC : 0 < UC) (hUI : 0 < UI) :
    (∀ γ : ℝ, Standing UC UI γ →
      ∀ (n : NoEntryPrices) (a : AccPrices), IsNoEntryEq UC n → IsAccEq UC UI γ a →
        (UI < UC → dPiY UC UI γ n a < dPiX UC UI γ n a) ∧
        (UC < UI → dPiX UC UI γ n a < dPiY UC UI γ n a)) ∧
    (UI < UC → ∃ γhat : ℝ, γhat < gammaMax UC UI ∧
      ∀ γ : ℝ, γhat < γ → Standing UC UI γ →
        ∀ (n : NoEntryPrices) (a : AccPrices) (e : EscPrices),
          IsNoEntryEq UC n → IsAccEq UC UI γ a → IsEscEq UC UI γ e →
          ∃ K : ℝ, 0 ≤ K ∧ AccommodationOutcome UC UI γ n a e K ∧
            integratedProfitA UC UI γ a - K < 0) := by sorry

end SystemSqueeze.Accommodation
