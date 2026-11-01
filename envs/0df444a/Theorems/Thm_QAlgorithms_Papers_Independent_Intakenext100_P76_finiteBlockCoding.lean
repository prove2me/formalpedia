-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P76_finiteBlockCoding
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P76.finiteBlockCoding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:48:57.019253+00:00
-- url     : https://prove2.me/theorems/d31de92c-ac8b-43cf-8bd2-7d118b72b886
-- title:
--   Finite-block iid pure-state coding bound
-- statement:
--   Let $W$, its normalized pure outputs, the measurable input law $\mu$, and the computed average output $\rho$ be as above. For an integer $n\ge1$, use the memoryless channel $W^{\otimes n}$ with product pure outputs and the iid input law $\mu^{\otimes n}$. For $0<\eta<\varepsilon<1$, a finite deterministic code and a joint POVM satisfy
--
--   $$
--   P_{\rm err}\le\varepsilon,\qquad
--   \log_2M\ge H_s^{\varepsilon-\eta}(\rho^{\otimes n})-\log_2\frac{4\varepsilon}{\eta^2}.
--   $$
--
--   Consequently the same lower bound holds for $\log_2M^*(W^{\otimes n},\varepsilon)$. This finite-block bound needs no moment or positive-variance hypothesis.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, PDF p. 9, §5, (5.1)–(5.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P76

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.9, (5.2): finite-block iid specialization. No variance, third moment,
or asymptotic approximation is assumed. The message decoder is joint. -/
theorem finiteBlockCoding {X : Type*} {I : Type} [MeasurableSpace X] [Countable I]
    (W : X → I → ℂ) (mu : Measure X) [IsProbabilityMeasure mu]
    (hnorm : ∀ x, IsUnitCoefficientVector (W x))
    (hmeas : ∀ a b, Measurable (fun x => Matrix.vecMulVec (W x) (star (W x)) a b))
    (p : ℕ → ℝ) (hspec : HasSpectralLaw (meanOutput W mu) p)
    (n : ℕ) (hn : 1 ≤ n) (epsilon slack : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hs : 0 < slack) (hse : slack < epsilon) :
    let R := spectralInfEntropy (productSpectrum p n) (epsilon - slack) -
      logTwo (4 * epsilon / slack ^ 2)
    HasFiniteCode (productPureCQChannel W n) epsilon R ∧
      (R : EReal) ≤ logMaxCodeSize (productPureCQChannel W n) epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P76

end
