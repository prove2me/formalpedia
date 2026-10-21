-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_lemmaOne
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.lemmaOne
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:53:20.27405+00:00
-- url     : https://prove2.me/theorems/e7ef78e0-ddb3-4dc1-9e28-ffaf44e7d20a
-- title:
--   Lemma 1: scalar asymptotic minimum
-- statement:
--   Let $b>0$, $c\in\mathbb R$, and $f(t)=2t+(1+t/2)/(1-t)$. There is $R(x)=o(x)$ such that, for every sufficiently large $x$, the minimum on the open interval $(0,1/2)$ is attained and
--
--   $$\min_{0<t<1/2} f(t)(x-b\log t+c)\le x+R(x).$$
--
--   This is an asymptotic assertion, with no attainment claim at arbitrary real $x$. It supplies the scalar optimization used in the oscillator continuity bounds.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 17, Lemma 1: scalar asymptotic minimum

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

/-- Lemma 1, PDF p.17: attained scalar minimum and x+o(x) bound only
EVENTUALLY as x tends to infinity, on the printed OPEN interval (0,1/2). -/
theorem lemmaOne (b c : ℝ) (hb : 0 < b) :
    ∃ R : ℝ → ℝ, Asymptotics.IsLittleO atTop R (fun x : ℝ => x) ∧
      ∀ᶠ x : ℝ in atTop, ∃ t : ℝ, t ∈ Set.Ioo 0 (1/2 : ℝ) ∧
        (∀ s ∈ Set.Ioo 0 (1/2 : ℝ),
          optimizationFactor t * (x - b * Real.log t + c) ≤
            optimizationFactor s * (x - b * Real.log s + c)) ∧
        optimizationFactor t * (x - b * Real.log t + c) ≤ x + R x := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
