-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_bounded_domination_refinements
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.bounded_domination_refinements
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:54:15.21178+00:00
-- url     : https://prove2.me/theorems/ea9956ee-fc07-4c03-b78d-f662453694e6
-- title:
--   Sharpness and reverse bounded functional domination: Remarks 11–12
-- statement:
--   Let f and g be convex normalized generators and fix the exact density bounds beta1,beta2 in [0,1). If g is positive away from 1 and both derivatives at 1 vanish, the restricted supremum of f/g is the least universal upper coefficient. Swapping Theorem 6's assumptions requires only f to be positive away from 1 and yields
--
--   $$D_g(P\|Q)\le \sup_{t\in S}\max\{g(t)/f(t),0\}\,D_f(P\|Q),\qquad S=(\beta_2,1)\cup(1,\beta_1^{-1}).$$
--
--   This is Remark 12's stated application of Theorem 6 with roles swapped. When g is also positive away from 1, the reciprocal infimum form (168) is included. If, further, f/g is increasing, both endpoint bounds (169)–(170) hold. Zero betas retain the infinite/open endpoints. All comparisons range over normalized probability pairs on arbitrary measurable alphabets.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 25, Sharpness and reverse bounded functional domination

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Sharpness and reverse bounded functional domination: Remarks 11–12, PDF p.25.
Remark 12 first swaps Theorem 6's assumptions: only f must be positive away from 1.
That comparison is stated directly as Dg <= sup(g/f) Df, whose scalar denominator
is nonzero. When g is also positive, retain (168)'s reciprocal infimum form;
both-positive monotone endpoint bounds (169)--(170) have their own guard. -/
theorem bounded_domination_refinements
    (f g : ℝ → ℝ) (hf : Generator f) (hg : Generator g)
    (b1 b2 : ℝ) (h1 : 0 ≤ b1 ∧ b1 < 1) (h2 : 0 ≤ b2 ∧ b2 < 1) :
    (PositiveGenerator g → (HasDerivAt f 0 1 ∧ HasDerivAt g 0 1) →
      Sharp (nDiv f) (nDiv g) (exactPairs b1 b2) (functionalConstant f g (scalarInterval b1 b2))) ∧
    (PositiveGenerator f →
      (∀ (A : Type u) [MeasurableSpace A] (P Q : Measure A)
        [IsProbabilityMeasure P] [IsProbabilityMeasure Q], exactPairs b1 b2 P Q →
          nDiv g P Q ≤ functionalConstant g f (scalarInterval b1 b2) * nDiv f P Q) ∧
      (PositiveGenerator g →
        (∀ (A : Type u) [MeasurableSpace A] (P Q : Measure A)
          [IsProbabilityMeasure P] [IsProbabilityMeasure Q], exactPairs b1 b2 P Q →
            (⨅ t : scalarInterval b1 b2, ENNReal.ofReal (f t / g t)) * nDiv g P Q ≤ nDiv f P Q) ∧
        (MonotoneOn (fun t => f t / g t) (Ioi 0 \ {1}) →
          ∀ (A : Type u) [MeasurableSpace A] (P Q : Measure A)
            [IsProbabilityMeasure P] [IsProbabilityMeasure Q], exactPairs b1 b2 P Q →
              ratioEndpoint f g (ENNReal.ofReal b2) * nDiv g P Q ≤ nDiv f P Q ∧
              nDiv f P Q ≤ ratioEndpoint f g ((ENNReal.ofReal b1)⁻¹) * nDiv g P Q))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
