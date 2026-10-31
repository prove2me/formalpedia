-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_lemma_4_2
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.lemma_4_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:10:03.830607+00:00
-- url     : https://prove2.me/theorems/4ec3605f-1e15-448f-a110-2a324a9f4334
-- title:
--   Lemma 4.2: uniform centered-quadratic small-ball estimate
-- statement:
--   For every $\kappa,\varepsilon>0$ there is a real constant $p(\kappa,\varepsilon)>0$, uniform over countably infinite coordinate sets and over all self-adjoint real trace-class operators $M$ with $\|M\|_1\le\kappa$, such that for the actual standard Gaussian cylinder law $\mu=\omega_I$,
--
--   $$\mu\{x:|q_M(x)-\operatorname{tr}M|<\varepsilon\}\ge p(\kappa,\varepsilon).$$
--
--   The quadratic is its canonical Gaussian representative. This is the uniform centered-quadratic small-ball estimate, including $M=0$ and all finite ranks.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 30, Lemma 4.2: uniform centered-quadratic small-ball estimate

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Lemma 4.2: the small-ball constant is uniform over the full trace-norm ball,
PDF pp.30–31. The zero operator is included. -/
theorem lemma_4_2 :
    ∀ kappa epsilon : ℝ, 0 < kappa → 0 < epsilon →
      ∃ p : ℝ, 0 < p ∧ ∀ (J : Type) [Countable J] [Infinite J] [DecidableEq J]
        (e : ℕ ≃ J) (A : RealCoordinateOperator J),
        ContinuousLinearMap.adjoint A = A → IsModulusTraceClass A → modulusTraceNorm A ≤ kappa →
          ENNReal.ofReal p ≤ (cylinderGaussian (1 : RealCoordinateOperator J))
            {x | |gaussianQuadratic e A x - basisOperatorTrace A| < epsilon} := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
