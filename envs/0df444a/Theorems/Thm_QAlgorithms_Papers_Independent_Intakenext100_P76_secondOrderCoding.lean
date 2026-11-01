-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P76_secondOrderCoding
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P76.secondOrderCoding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:49:31.306349+00:00
-- url     : https://prove2.me/theorems/7dded3ec-b865-4fdd-bf2a-e09e868267eb
-- title:
--   Second-order achievability for a fixed pure-state ensemble
-- statement:
--   Fix a separable-output pure-state cq channel $W$, a measurable probability law $\mu$ on its input alphabet, and $0<\varepsilon<1$. Let $\rho$ be the average output, with eigenvalue law $p_Z$. Assume the self-information $L=-\log_2p_Z(Z)$ has finite mean and finite third absolute moment. Write $H(\rho)=\mathbb E L$, $V(\rho)=\mathbb E[(L-H(\rho))^2]$, and let $\Phi^{-1}$ be the standard-normal quantile. There exist $C>0$ and an integer $N\ge2$, depending on the fixed channel, law and error, such that every $n\ge N$ admits an actual finite code with average error at most $\varepsilon$ and
--
--   $$
--   \log_2M\ge nH(\rho)+\sqrt{nV(\rho)}\,\Phi^{-1}(\varepsilon)-C\log_2n.
--   $$
--
--   The same lower bound holds for the supremum $\log_2M^*$. This is achievability for the specified ensemble and includes $V(\rho)=0$.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, PDF p. 9, §5, (5.3)

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

/-- PDF p.9, (5.3), with the Berry–Esseen moment convention on pp.4–5.
Constants depend on the fixed channel, law and error, and precede n. Finite
third absolute self-information moment is explicit; zero variance is included.
This is achievability for the given ensemble, with no capacity-optimality claim. -/
theorem secondOrderCoding {X : Type*} {I : Type} [MeasurableSpace X] [Countable I]
    (W : X → I → ℂ) (mu : Measure X) [IsProbabilityMeasure mu]
    (hnorm : ∀ x, IsUnitCoefficientVector (W x))
    (hmeas : ∀ a b, Measurable (fun x => Matrix.vecMulVec (W x) (star (W x)) a b))
    (p : ℕ → ℝ) (hspec : HasSpectralLaw (meanOutput W mu) p)
    (hmean : Summable (fun j => p j * (-logTwo (p j))))
    (hthird : Summable (fun j => p j * |logTwo (p j)| ^ 3))
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let R := (n : ℝ) * selfInformationMean p +
        Real.sqrt ((n : ℝ) * selfInformationVariance p) * normalQuantile epsilon -
        C * logTwo (n : ℝ)
      HasFiniteCode (productPureCQChannel W n) epsilon R ∧
        (R : EReal) ≤ logMaxCodeSize (productPureCQChannel W n) epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P76

end
