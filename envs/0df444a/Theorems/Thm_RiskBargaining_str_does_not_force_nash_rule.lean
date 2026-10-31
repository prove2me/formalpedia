-- Prove2me | Theorems.Thm_RiskBargaining_str_does_not_force_nash_rule
-- name    : RiskBargaining.str_does_not_force_nash_rule
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:32:05.95875+00:00
-- url     : https://prove2.me/theorems/acdd7841-976d-48ca-9abe-40785a6f2686
-- title:
--   Appendix A.3, p.37 (corrected: counterexample) — Axioms 1–3 do not force (9) at irrational values
-- statement:
--   Fix a probability space, $p\ge 1$ and a nonempty compact $\mathcal X$. There is a single bargaining solution $F$, defined on all finite nonempty player sets, that satisfies PAR, SYM and STR at every admissible instance and differs from (9) at some admissible instance.
--
--   The witness is the rule $F_i=v_i+w_i\big(z-\sum_j v_j\big)$ with $w_i=c(v_i)v_i/\sum_j c(v_j)v_j$, where $c(t)=1$ for rational $t$ and $c(t)=2$ otherwise. It differs from (9) at $v=(1,\sqrt2)$, $z=10$.
--
--   The paper asserts the opposite. This statement is the reason for the axiom CONT in the corrected Theorem 1.
--
--   Differences from the source:
--   - correction: for v_i ∉ ℚ, (9) follows from Axioms 1 – 3 by continuity of the right hand side of (9) → there is a bargaining solution satisfying PAR, SYM, STR that differs from (9); reason: the continuity of the right hand side says nothing about F; the printed step is false, and this item is its refutation
--   - reading: X, Y and p are not listed in an instance; a bargaining solution acts on instances → X, Y, p are fixed parameters; F is a family over all finite nonempty player types; reason: Definition 2 lists only (R, M, 𝒜), and Axiom 3 changes the player set
--   - encoding: M : 𝒳 × Ω → ℝ → M : X → Lp ℝ p μ; reason: Assumption 1 makes x ↦ M_x a map into L^p
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.3, proof of Theorem 1, p.37

import Mathlib
import Definitions.Def_RiskBargaining_IsBargainingSolution
import Definitions.Def_RiskBargaining_PAR
import Definitions.Def_RiskBargaining_SYM
import Definitions.Def_RiskBargaining_STR
import Definitions.Def_RiskBargaining_nashRule

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **Counterexample: Axioms 1–3 do not force (9) at irrational values.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.3, proof of Theorem 1, p.37, claims: "For vi ∉ ℚ, the assertion follows because of the
continuity of the functions on the right hand side of (9)". That continuity says nothing about `F`.

On every probability space, every `p ≥ 1` and every nonempty compact `X`, there is one family `F`, over
all player types, that is a bargaining solution, satisfies PAR, SYM and STR at every admissible
instance, and differs from (9) at some admissible instance. -/
theorem str_does_not_force_nash_rule {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X] [Nonempty X] :
    ∃ F : Rule μ p X, IsBargainingSolution F ∧ PAR F ∧ SYM F ∧ STR F ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Nonempty ι) (I : Instance μ p X ι),
        I.Admissible ∧ F ι I ≠ nashRule ι I := by sorry

end RiskBargaining
