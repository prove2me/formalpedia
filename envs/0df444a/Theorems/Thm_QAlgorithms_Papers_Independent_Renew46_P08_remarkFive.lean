-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkFive
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkFive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:52:27.23882+00:00
-- url     : https://prove2.me/theorems/14054d1e-1868-46c6-af5b-43abbe527386
-- title:
--   Remark 5: asymptotic oscillator QCMI optimization
-- statement:
--   Fix a positive mode count, positive oscillator constants and $0<\varepsilon\le1$. Write $\widehat F(E)=\ell\log((E+E_0)/(\ell E_*))+\ell$ and $r_\varepsilon(t)=(1+t/2)/(1-\varepsilon t)$. There exists a real remainder $R(E)=o(\widehat F(E))$ such that, for every sufficiently large $E$, some $0<t\le1/(2\varepsilon)$ satisfies
--
--   $$2\varepsilon(2t+r_\varepsilon(t))[\widehat F(E)-\ell\log(\varepsilon t)]\le\varepsilon[2\widehat F(E)+R(E)].$$
--
--   Thus the main term in the oscillator QCMI bound admits the source's leading coefficient two. The parameter $t$ may be chosen for each energy.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 17, Remark 5: asymptotic oscillator QCMI optimization

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

/-- Remark 5, PDF p.17: appropriate t may depend on energy; all oscillator
parameters and positive epsilon are fixed before the large-coefficientEnergy limit. -/
theorem remarkFive {ell : ℕ} (hell : 0 < ell) (hbar : ℝ) (hhbar : 0 < hbar)
    (omega : Fin ell → ℝ) (homega : ∀ i, 0 < omega i)
    (epsilon : ℝ) (heps : 0 < epsilon) (hepsone : epsilon ≤ 1) :
    ∃ R : ℝ → ℝ, Asymptotics.IsLittleO atTop R (oscillatorEnvelope hbar omega) ∧
      ∀ᶠ E : ℝ in atTop, ∃ t : ℝ, 0 < t ∧ t ≤ 1/(2*epsilon) ∧
        oscillatorMain 2 hbar omega E epsilon t ≤
          epsilon * (2 * oscillatorEnvelope hbar omega E + R E) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
