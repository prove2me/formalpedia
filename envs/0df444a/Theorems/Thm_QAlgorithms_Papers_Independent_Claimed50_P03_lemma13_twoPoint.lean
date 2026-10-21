-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma13_twoPoint
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma13_twoPoint
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:04:53.500423+00:00
-- url     : https://prove2.me/theorems/d623fee0-906a-4aa0-b286-795b0bb298f2
-- title:
--   Lemma 13 (Le Cam two-point method)
-- statement:
--   Let $p_0,p_1$ be probability measures on a measurable domain $\Omega$, and define
--   $$d_{\rm TV}(p_0,p_1)=\sup_{S\text{ measurable}}|p_0(S)-p_1(S)|.$$
--   If $d_{\rm TV}(p_0,p_1)<1/3$, no measurable function $A:\Omega\to[0,1]$ satisfies both
--   $$\int(1-A(x))\,dp_0(x)\ge\frac23,\qquad\int A(x)\,dp_1(x)\ge\frac23.$$
--   Here $A(x)$ is the conditional probability that a randomized binary test outputs one on input $x$; the two integrals are its success probabilities under hypotheses zero and one.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 34, Lemma 13 (Le Cam two-point method)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Paper p.34, Lemma 13: no binary test succeeds with probability at least
2/3 under both laws when their total variation distance is strictly below 1/3.
A(x) is the measurable conditional probability of output 1, allowing arbitrary
classical randomization. The printed unused existence of a distribution D adds
no restriction, since p0 itself is a probability distribution. -/
theorem lemma13_twoPoint {Omega : Type*} [MeasurableSpace Omega]
    (p0 p1 : Measure Omega) [IsProbabilityMeasure p0] [IsProbabilityMeasure p1]
    (hclose : classicalTVDistance p0 p1 < 1 / 3) :
    ¬ ∃ A : Omega → ℝ, Measurable A ∧ (∀ x, 0 ≤ A x ∧ A x ≤ 1) ∧
      (2 / 3 : ℝ) ≤ (∫ x, 1 - A x ∂p0) ∧
      (2 / 3 : ℝ) ≤ (∫ x, A x ∂p1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
