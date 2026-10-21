-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkOne
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkOne
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:45:44.109695+00:00
-- url     : https://prove2.me/theorems/9ee6ab01-a6d4-4cff-a0f3-e5cecfd5ea7f
-- title:
--   Remark 1: alternate QMI continuity bound
-- statement:
--   Let $d=\min\{\dim A,\dim B\}<\infty$ and $\rho,\sigma$ be bipartite states. Their mutual informations are finite. For $d\ge2$ and $\varepsilon=\frac12\|\rho-\sigma\|_1\le1-1/d$,
--
--   $$|I(A:B)_\rho-I(A:B)_\sigma|\le\varepsilon\log(d-1)+2\varepsilon\log d+h_2(\varepsilon)+g(\varepsilon).$$
--
--   Here $h_2$ is binary entropy in nats and $g(x)=(1+x)\log(1+x)-x\log x$. For $d=1$ both mutual informations are zero. Since $h_2(\varepsilon)<g(\varepsilon)$ for positive $\varepsilon\le1$, the displayed bound improves (25) at $d=2$.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 11, Remark 1: alternate QMI continuity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Remark 1, PDF p.11: alternate QMI bound at the finite MINIMUM local
dimension. The one-dimensional case is separately zero; log(d-1) is used only
for d>=2. The last clause records the strict improvement at d=2. -/
theorem remarkOne {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (d : ℕ) (hd : FiniteMinDimension I J d) (rho sigma : State (I × J)) :
    qmi rho.coefficients < ⊤ ∧ qmi sigma.coefficients < ⊤ ∧
    (d = 1 → qmi rho.coefficients = 0 ∧ qmi sigma.coefficients = 0) ∧
    (2 ≤ d → let epsilon := (extendedHalfTraceDistance rho.coefficients sigma.coefficients).toReal
      epsilon ≤ 1 - 1 / (d : ℝ) →
      |(qmi rho.coefficients).toReal - (qmi sigma.coefficients).toReal| ≤
        epsilon * Real.log ((d : ℝ) - 1) + 2 * epsilon * Real.log d +
          Real.binEntropy epsilon + g epsilon) ∧
    (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → Real.binEntropy epsilon < g epsilon) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
