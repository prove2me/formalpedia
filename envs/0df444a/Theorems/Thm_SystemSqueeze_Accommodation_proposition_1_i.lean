-- Prove2me | Theorems.Thm_SystemSqueeze_Accommodation_proposition_1_i
-- name    : SystemSqueeze.Accommodation.proposition_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:15.150703+00:00
-- url     : https://prove2.me/theorems/caf16da4-cafc-4979-b845-9c30ec9e3e1e
-- title:
--   Proposition 1 (i), p. 16 — thresholds 0 < K̲ < K̄: A enters iff K ≤ K̄, B iff K ≤ K̲; accommodation iff K̲ < K ≤ K̄, escalation iff K ≤ K̲
-- statement:
--   Let $U_C,U_I,\gamma$ satisfy the standing assumptions, and fix Nash equilibrium price profiles of the no-entry, accommodation and escalation subgames. Define the thresholds
--   $$\bar K=\Pi_A^{(ii)}-\Pi_A^{(i)},\qquad \underline K=\Pi_B^{(iii)}-\Pi_B^{(ii)},$$
--   the values of $K$ at which $A$'s entry benefit (2) and $B$'s entry benefit (3) vanish. Then
--   $$0<\underline K<\bar K,$$
--   and for every entry cost $K\ge 0$:
--
--   1. $A$ enters when $B$ stays out (benefit (2) $\ge 0$) if and only if $K\le\bar K$;
--   2. $B$ enters when $A$ is in (benefit (3) $\ge 0$) if and only if $K\le\underline K$;
--   3. the stage-1 outcome is accommodation if and only if $\underline K<K\le\bar K$;
--   4. the stage-1 outcome is escalation if and only if $K\le\underline K$.
--
--   The result shows that the asymmetric accommodation outcome occupies a nonempty intermediate range of entry costs.
--
--   **Formalization Note** The proposition as printed says accommodation occurs for $K\in[\bar K,\underline K)$, an empty interval since $\bar K>\underline K$; its proof (p. 34) says "for $\underline K<K\le\bar K$ … an accommodation equilibrium occurs", which is what is stated here. The positivity $\underline K>0$ is from the proof ("we obtain that $\bar K>\underline K>0$"). An indifferent firm enters, as in the proof. $K\ge0$ is added (an investment).
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), p. 16 (PDF 17), Proposition 1 (i); proof pp. 33–34 (PDF 34–35), (2)–(4)

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

namespace SystemSqueeze.Accommodation

/-- Proposition 1 (i), p. 16, with its proof, pp. 33–34. With `K̄` the value of `K` at which
`A`'s entry benefit (2) vanishes and `K̲` the value at which `B`'s entry benefit (3) vanishes:
`0 < K̲ < K̄`; `A` enters (given `B` stays out) iff `K ≤ K̄`; `B` enters (given `A` is in) iff
`K ≤ K̲`; accommodation occurs iff `K̲ < K ≤ K̄` (the printed interval `[K̄, K̲)` is a slip, the
proof has `K̲ < K ≤ K̄`); escalation occurs iff `K ≤ K̲`. -/
theorem proposition_1_i (UC UI γ : ℝ) (h : Standing UC UI γ)
    (n : NoEntryPrices) (a : AccPrices) (e : EscPrices)
    (hn : IsNoEntryEq UC n) (ha : IsAccEq UC UI γ a) (he : IsEscEq UC UI γ e)
    (Kbar Kund : ℝ) (hKbar : Kbar = benefitA UC UI γ n a 0)
    (hKund : Kund = benefitB UC UI γ a e 0) :
    0 < Kund ∧ Kund < Kbar ∧
    ∀ K : ℝ, 0 ≤ K →
      (0 ≤ benefitA UC UI γ n a K ↔ K ≤ Kbar) ∧
      (0 ≤ benefitB UC UI γ a e K ↔ K ≤ Kund) ∧
      (AccommodationOutcome UC UI γ n a e K ↔ Kund < K ∧ K ≤ Kbar) ∧
      (EscalationOutcome UC UI γ a e K ↔ K ≤ Kund) := by sorry

end SystemSqueeze.Accommodation
