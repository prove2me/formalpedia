-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P33_localAbsoluteContinuityIffCorners
-- name    : QAlgorithms.Papers.Independent.Next46.P33.localAbsoluteContinuityIffCorners
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:29:30.079601+00:00
-- url     : https://prove2.me/theorems/35666e37-d6b0-4663-a289-249f110ca10c
-- title:
--   Local absolute continuity is continuity on each finite corner
-- statement:
--   Let $M$ be an arbitrary von Neumann algebra, let $\phi_1$ be a faithful normal semifinite weight, and let $\phi_0$ be a normal weight that is semifinite on the atomic summand of $M$. Then
--
--   $$
--   \bigl[\forall e\in\operatorname{Proj}(M),\ \phi_1(e)<\infty\Rightarrow\phi_0(e)<\infty\bigr]
--   \quad\Longleftrightarrow\quad
--   \bigl[\forall e\in\operatorname{Proj}(M),\ \phi_1(e)<\infty\Rightarrow
--   \forall\varepsilon>0\;\exists\delta>0\;\forall f\in\operatorname{Proj}(M),
--   f\le e\ \land\ \phi_1(f)<\delta\Rightarrow\phi_0(f)<\varepsilon\bigr].
--   $$
--
--   The modulus on the right may depend on the corner $e$ and on $\varepsilon$. This equivalence gives the local absolute-continuity condition its quantitative meaning; global semifiniteness of $\phi_0$ is not an assumption.
-- source:
--   Composition Operators on Haagerup $L^p$-spaces, arXiv:math/0603612v2, PDF p. 5, Theorem 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P33

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Theorem 3.5, PDF pp.5--6. Local preservation of finite projections is
equivalent to epsilon-delta continuity on every phi1-finite corner. Only the
atomic part of phi0 is assumed semifinite. -/
theorem localAbsoluteContinuityIffCorners
    (M : VonNeumannAlgebra H) (phi1 phi0 : Weight M)
    (hNormal1 : IsNormalWeight phi1) (hFaithful1 : IsFaithfulWeight phi1)
    (hSemifinite1 : IsSemifiniteWeight phi1)
    (hNormal0 : IsNormalWeight phi0) (hAtomic0 : IsSemifiniteOnAtomicPart phi0) :
    WeightLocallyAbsolutelyContinuous phi0 phi1 ↔
      ∀ e : Projection M, phi1.value (projectionPositive e) < ⊤ →
        CornerWeightEpsilonDelta phi0 phi1 e := by sorry

end QAlgorithms.Papers.Independent.Next46.P33

end
