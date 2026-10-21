-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P23_factorizationCriterionCorrected
-- name    : QAlgorithms.Papers.Independent.Renew46.P23.factorizationCriterionCorrected
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:34:05.431355+00:00
-- url     : https://prove2.me/theorems/e249fdd5-17bc-4275-9877-9f9763664565
-- title:
--   Factorization criterion with the common-measure correction
-- statement:
--   Let $\{P_\theta:\theta\in\Theta\}$ be a nonempty family of probability measures on $(X,\mathcal A)$, all absolutely continuous with respect to a $\sigma$-finite measure $\mu$. Let $T:(X,\mathcal A)\to(Y,\mathcal B)$ be measurable. The statistic $T$ is sufficient if and only if there exist finite nonnegative measurable functions $h:X\to[0,\infty)$ and $g_\theta:Y\to[0,\infty)$ such that, for every $\theta$,
--
--   $$\frac{dP_\theta}{d\mu}(x)=g_\theta(T(x))h(x)\qquad\mu\text{-almost everywhere}.$$
--
--   The common factor $h$ is chosen for the whole family. This is the common-measure factorization criterion.
--
--   **Source correction.** The printed proposition says $P_\theta$-almost everywhere. It is changed here to $\mu$-almost everywhere: the printed condition fails to control zeros off each state's support and admits a constant statistic for two disjoint point masses. The printed claim remains deferred; this corrected statement requires independent moderation.
-- source:
--   Sufficiency in quantum statistical inference. A survey with examples, arXiv:quant-ph/0604091v1, PDF p. 6, Proposition 3: corrected common-measure factorization criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P23

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Renew46.P23

open QAlgorithms.Papers.Independent.Next46.P43
  (SufficientSigmaAlgebra MinimalSufficientSigmaAlgebra IsCStarCoarseGraining)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

local instance : MeasurableSpace Bool := ⊤

/-- Proposition 3, PDF p.6, with an explicit source correction.
Printed: the density factorization holds P_theta-almost everywhere.
Changed: it holds mu-almost everywhere for each theta. Why: disjoint point
masses with a constant statistic satisfy the printed condition but are not
sufficient. Finite nonnegative measurable versions of both factors are used.
The printed proposition is separately deferred. Independent moderation is required. -/
theorem factorizationCriterionCorrected
    {X Y Theta : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    [Nonempty Theta] (P : Theta → Measure X)
    (hProb : ∀ theta, IsProbabilityMeasure (P theta))
    (mu : Measure X) [SigmaFinite mu] (hDom : ∀ theta, P theta ≪ mu)
    (T : X → Y) (hT : Measurable T) :
    SufficientSigmaAlgebra P (MeasurableSpace.comap T mY) ↔
      ∃ (h : X → ℝ≥0) (g : Theta → Y → ℝ≥0),
        Measurable h ∧ (∀ theta, Measurable (g theta)) ∧
        ∀ theta, (P theta).rnDeriv mu =ᵐ[mu]
          (fun x => (g theta (T x) : ℝ≥0∞) * (h x : ℝ≥0∞)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P23

end
