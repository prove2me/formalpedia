-- Prove2me | Theorems.Thm_SemialgebraicSDP_Copositive_Supplement_theorem_3_1
-- name    : SemialgebraicSDP.Copositive.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:43:43.51509+00:00
-- url     : https://prove2.me/theorems/d771491f-4b6f-4081-91ea-081cbace9cb8
-- title:
--   Theorem 3.1 (corrected: opposite-side feasibility) — near-zero duality gap and joint attainment
-- statement:
--   Let $A_i,C\in\mathcal S^n$ and $b\in\mathbb R^m$. Consider the primal-dual pair (3.1)–(3.2). If both problems are feasible and at least one is strictly feasible, then
--   $$\forall\epsilon>0\ \exists X,y\text{ feasible}:\quad \operatorname{tr}(CX)-\sum_i b_i y_i<\epsilon.$$
--   If both problems are strictly feasible, there are feasible $X_\star,y_\star$ attaining the minimum and maximum, with equal objectives. Both clauses are included in one item. This is a background companion theorem, with no claimed use in the proof of the published goal.
--
--   **Formalization Note** The source's first clause is false without feasibility of the opposite side: $n=m=1$, $A_1=0$, $b_1=1$, $C=1$ gives strictly feasible dual slack $1$ and an empty primal set. The correction excludes exactly such infeasible pairs from the near-gap assertion; the attainment clause needs no added feasibility premise. “Nonempty interior” is interpreted as a positive definite feasible matrix/slack, as the preceding paragraph's “strictly feasible points” indicates, rather than ambient interior of an equality-constrained matrix set. No optimal value uses a totalized infimum.
--
--   Differences from the source:
--   - correction: one feasible set has nonempty interior → both sides feasible and at least one strictly feasible in the near-gap clause; reason: the printed claim fails for A₁=0, b₁=1, C=1; feasibility is necessary for the conclusion itself.
--   - reading: nonempty interior of the feasible set → positive definite primal matrix or dual slack; reason: the preceding paragraph on p. 296 identifies the intended constraint qualification as existence of strictly feasible points.
--   - encoding: optimal solutions are achieved → explicit feasible X,y, equal objectives, and universal minimum/maximum inequalities; reason: retains attainment without totalized sInf/sSup.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 297, Theorem 3.1

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Supplement_SDPPair

namespace SemialgebraicSDP.Copositive.Supplement

/-- Theorem 3.1, corrected: one strict side also requires feasibility of the other.
The second clause retains joint attainment under strict feasibility of both sides. -/
theorem theorem_3_1 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) :
    (((∃ X, PrimalFeasible A b X) ∧ (∃ y, DualFeasible A C y) ∧
        (PrimalStrict A b ∨ DualStrict A C)) →
      ∀ ε : ℝ, 0 < ε → ∃ X y, PrimalFeasible A b X ∧ DualFeasible A C y ∧
        tracePair C X - ∑ i, b i * y i < ε) ∧
    ((PrimalStrict A b ∧ DualStrict A C) →
      ∃ X y, PrimalFeasible A b X ∧ DualFeasible A C y ∧
        tracePair C X = ∑ i, b i * y i ∧
        (∀ Z, PrimalFeasible A b Z → tracePair C X ≤ tracePair C Z) ∧
        (∀ w, DualFeasible A C w → (∑ i, b i * w i) ≤ ∑ i, b i * y i)) := by sorry

end SemialgebraicSDP.Copositive.Supplement
