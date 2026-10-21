-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P33_cornersImplyLocalAbsoluteContinuity
-- name    : QAlgorithms.Papers.Independent.Next46.P33.cornersImplyLocalAbsoluteContinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:29:58.737795+00:00
-- url     : https://prove2.me/theorems/84cb09da-0d11-4c92-99cb-595e7f86cd5f
-- title:
--   The reverse corner implication does not require normality of the second weight
-- statement:
--   Let $M$ be a von Neumann algebra, let $\phi_1$ be a faithful normal semifinite weight, and let $\phi_0$ be a weight that is semifinite on the atomic summand of $M$. Assume that for every projection $e$ with $\phi_1(e)<\infty$ and every $\varepsilon>0$ there exists $\delta>0$ such that every projection $f\le e$ satisfying $\phi_1(f)<\delta$ also satisfies $\phi_0(f)<\varepsilon$. Then
--
--   $$
--   \forall e\in\operatorname{Proj}(M),\qquad
--   \phi_1(e)<\infty\ \Longrightarrow\ \phi_0(e)<\infty.
--   $$
--
--   Normality of $\phi_0$ is not required. This is the explicit refinement of the reverse implication following the proof of Theorem 3.5.
-- source:
--   Composition Operators on Haagerup $L^p$-spaces, arXiv:math/0603612v2, PDF p. 6, Theorem 3.5: unnumbered reverse-implication refinement

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P33

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Theorem 3.5, final observation, PDF p.6. The reverse implication does
not use normality of phi0. Its atomic semifiniteness assumption is retained. -/
theorem cornersImplyLocalAbsoluteContinuity
    (M : VonNeumannAlgebra H) (phi1 phi0 : Weight M)
    (hNormal1 : IsNormalWeight phi1) (hFaithful1 : IsFaithfulWeight phi1)
    (hSemifinite1 : IsSemifiniteWeight phi1)
    (hAtomic0 : IsSemifiniteOnAtomicPart phi0)
    (hCorners : ∀ e : Projection M, phi1.value (projectionPositive e) < ⊤ →
      CornerWeightEpsilonDelta phi0 phi1 e) :
    WeightLocallyAbsolutelyContinuous phi0 phi1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P33

end
