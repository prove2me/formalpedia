-- Prove2me | Theorems.Thm_RiskBargaining_nash_rule_axioms
-- name    : RiskBargaining.nash_rule_axioms
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:32:07.856072+00:00
-- url     : https://prove2.me/theorems/684584e6-c104-4cc9-add6-2570d0f75dfc
-- title:
--   Appendix A.3, p.37 (corrected: CONT added, on the admissible class) — (9) is a bargaining solution and satisfies the axioms
-- statement:
--   1. The rule (9) is a bargaining solution: it takes values in $\mathcal U(R,M,\mathcal A)$ at every admissible instance.
--   2. Every bargaining solution that agrees with (9) at every admissible instance satisfies PAR, SYM, STR and CONT.
--
--   These are clauses (a) and (b) of the corrected Theorem 1. They show that the hypotheses of the characterization can be met.
--
--   Differences from the source:
--   - correction: (9) implies Axioms 1 – 3, for every feasible instance → (9) on the admissible class implies PAR, SYM, STR and CONT, and (9) is shown to be a bargaining solution; reason: CONT is needed for the converse direction (see RiskBargaining.str_does_not_force_nash_rule), and the max in (8) can fail to exist (see RiskBargaining.proposition_1_counterexample)
--   - generalization: p ≥ 1 → p : ℝ≥0∞ with 1 ≤ p, so p = ∞ is admitted; reason: the page does not say whether p = ∞ is meant; finite p is a special case
--   - reading: X, Y and p are not listed in an instance; a bargaining solution acts on instances → X, Y, p are fixed parameters; F is a family over all finite nonempty player types; reason: Definition 2 lists only (R, M, 𝒜), and Axiom 3 changes the player set
--   - encoding: M : 𝒳 × Ω → ℝ; N′ = N∖{i} ∪ {(i,k) | k = 1,…,ℓ} → M : X → Lp ℝ p μ; player type {j // j ≠ i} ⊕ Fin ℓ with ℓ : ℕ+; reason: the same instances and the same game
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.3, proof of Theorem 1, p.37

import Mathlib
import Definitions.Def_RiskBargaining_IsBargainingSolution
import Definitions.Def_RiskBargaining_PAR
import Definitions.Def_RiskBargaining_SYM
import Definitions.Def_RiskBargaining_STR
import Definitions.Def_RiskBargaining_ContScaling
import Definitions.Def_RiskBargaining_nashRule

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **Clauses (a) and (b) of the corrected Theorem 1: rule (9) is a bargaining solution and meets the
axioms.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.3, proof of Theorem 1, p.37.

(a) Rule (9) is a bargaining solution. (b) Every bargaining solution that agrees with (9) on the
admissible class satisfies PAR, SYM, STR and CONT.

**Formalization Note.** The page shows PAR, SYM and STR. CONT is added to the list because the corrected
"only if" uses it. -/
theorem nash_rule_axioms {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    IsBargainingSolution (nashRule : Rule μ p X) ∧
      ∀ F : Rule μ p X, IsBargainingSolution F →
        (∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι),
          I.Admissible → F ι I = nashRule ι I) →
        PAR F ∧ SYM F ∧ STR F ∧ ContScaling F := by sorry

end RiskBargaining
