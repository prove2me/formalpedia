-- Prove2me | Theorems.Thm_RiskBargaining_theorem_1
-- name    : RiskBargaining.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:31:47.008001+00:00
-- url     : https://prove2.me/theorems/fd3782bc-1b13-4839-b8c1-6ee4a00394ce
-- title:
--   Theorem 1 (corrected: CONT added, and the max in (8) must exist) — Axioms 1–3 with continuity characterize the allocation proportional to endowment acceptabilities
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $p\ge 1$, and $\mathcal X$ a compact topological space. Call an instance $(R,M,\mathcal A)$ **admissible** if $v_i=\mathcal A_i(R_i)>0$ for all $i$ and the maximum $z=z(R,M,\mathcal A)$ in (8) exists. On the admissible class:
--
--   1. (a) The rule
--   $$
--   u_i=\frac{v_i}{\sum_{j=1}^n v_j}\cdot z(R,M,\mathcal A),\qquad i\in N, \tag{9}
--   $$
--   is a bargaining solution.
--   2. (b) Every bargaining solution that agrees with (9) satisfies PAR, SYM, STR and CONT.
--   3. (c) Every bargaining solution that satisfies PAR, SYM and STR agrees with (9) at every instance whose values are natural multiples of one positive real.
--   4. (d) Every bargaining solution that satisfies PAR, SYM, STR and CONT agrees with (9) at every instance.
--
--   Clauses (a), (b), (d) are the printed equivalence with CONT added, and (c) is what the printed axioms alone give. The theorem identifies a unique acceptability allocation for risk-averse players sharing a joint random profit.
--
--   Differences from the source:
--   - correction: a bargaining solution satisfying Axioms 1 – 3 is given by (9) at every instance → CONT is added in clause (d), and clause (c) gives (9) without CONT at commensurable values; reason: the printed claim is false; see RiskBargaining.str_does_not_force_nash_rule (one-point space, v = (1, √2), z = 10)
--   - correction: z is defined by the max in (8), on every feasible instance → the class requires the max in (8) to exist; reason: the max can fail to exist, and then no F satisfies PAR at that instance; see RiskBargaining.proposition_1_counterexample
--   - reading: X, Y and p are not listed in an instance; a bargaining solution acts on instances → X, Y, p are fixed parameters; F is a family over all finite nonempty player types; reason: Definition 2 lists only (R, M, 𝒜), and Axiom 3 changes the player set
--   - encoding: M : 𝒳 × Ω → ℝ; N′ = N∖{i} ∪ {(i,k) | k = 1,…,ℓ} → M : X → Lp ℝ p μ; player type {j // j ≠ i} ⊕ Fin ℓ with ℓ : ℕ+; reason: the same instances and the same game
--   - generalization: v_i ∈ ℚ in the first step of the proof; p ≥ 1 → Commensurable in clause (c); p = ∞ admitted; reason: every rational family is commensurable; finite p is a special case
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Theorem 1, p.10

import Mathlib
import Definitions.Def_RiskBargaining_IsBargainingSolution
import Definitions.Def_RiskBargaining_PAR
import Definitions.Def_RiskBargaining_SYM
import Definitions.Def_RiskBargaining_STR
import Definitions.Def_RiskBargaining_ContScaling
import Definitions.Def_RiskBargaining_nashRule
import Definitions.Def_RiskBargaining_Instance_Commensurable

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **Theorem 1, corrected: Axioms 1–3 with CONT characterize the rule (9) on the admissible class.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Theorem 1, p.10.

For the class of admissible instances (values positive, the max in (8) exists, Assumption 1):

* (a) rule (9), `u_i = v_i / (∑_j v_j) · z`, is a bargaining solution;
* (b) a bargaining solution that agrees with (9) on the class satisfies PAR, SYM, STR and CONT;
* (c) a bargaining solution satisfying PAR, SYM, STR agrees with (9) at every admissible instance whose
  values are commensurable;
* (d) a bargaining solution satisfying PAR, SYM, STR and CONT agrees with (9) at every admissible instance.

**Formalization Note.** The printed theorem is the equivalence of "Axioms 1–3" and (9) at every instance.
Its "only if" fails at incommensurable values (`RiskBargaining.str_does_not_force_nash_rule`), hence CONT in
(d) and the restriction in (c); its `z` need not exist (`RiskBargaining.proposition_1_counterexample`),
hence `Attained` in the class. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    IsBargainingSolution (nashRule : Rule μ p X) ∧
    (∀ F : Rule μ p X, IsBargainingSolution F →
      (∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι),
        I.Admissible → F ι I = nashRule ι I) →
      PAR F ∧ SYM F ∧ STR F ∧ ContScaling F) ∧
    (∀ F : Rule μ p X, IsBargainingSolution F → PAR F → SYM F → STR F →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι),
        I.Admissible → I.Commensurable → F ι I = nashRule ι I) ∧
    (∀ F : Rule μ p X, IsBargainingSolution F → PAR F → SYM F → STR F → ContScaling F →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι),
        I.Admissible → F ι I = nashRule ι I) := by sorry

end RiskBargaining
