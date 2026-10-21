-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkTen
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkTen
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:05:09.882195+00:00
-- url     : https://prove2.me/theorems/56d07d84-b047-4293-9775-652c299f4919
-- title:
--   Remark 10: asymptotic oscillator Holevo optimization
-- statement:
--   Fix an $\ell\ge1$ mode oscillator with positive physical constants and fix $0<\varepsilon\le1$. With its envelope $\widehat F(E)=\ell\log((E+E_0)/(\ell E_*))+\ell$, there is $R(E)=o(\widehat F(E))$ such that, for sufficiently large $E$, some admissible $0<t\le1/(2\varepsilon)$ satisfies
--
--   $$\varepsilon(2t+r_\varepsilon(t))[\widehat F(E)-\ell\log(\varepsilon t)]\le\varepsilon[\widehat F(E)+R(E)].$$
--
--   This optimizes the main term in the Holevo bound with coefficient one. The oscillator and accuracy parameters stay fixed during the energy limit.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 29, Remark 10: asymptotic oscillator Holevo optimization

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

/-- Remark 10, PDF p.29: coefficient ONE in oscillator Holevo optimization. -/
theorem remarkTen {ell : ℕ} (hell : 0 < ell) (hbar : ℝ) (hhbar : 0 < hbar)
    (omega : Fin ell → ℝ) (homega : ∀ i, 0 < omega i)
    (epsilon : ℝ) (heps : 0 < epsilon) (hepsone : epsilon ≤ 1) :
    ∃ R : ℝ → ℝ, Asymptotics.IsLittleO atTop R (oscillatorEnvelope hbar omega) ∧
      ∀ᶠ E : ℝ in atTop, ∃ t : ℝ, 0 < t ∧ t ≤ 1/(2*epsilon) ∧
        oscillatorMain 1 hbar omega E epsilon t ≤
          epsilon * (oscillatorEnvelope hbar omega E + R E) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
