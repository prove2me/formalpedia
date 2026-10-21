-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_propositionTwo
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.propositionTwo
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:44:23.015412+00:00
-- url     : https://prove2.me/theorems/c60684dd-3ace-4b3d-8b94-4c9e15ef9d31
-- title:
--   Proposition 2, (35): optimized energy-constrained QCMI continuity; original seed
-- statement:
--   Let $A,B,C$ be nonzero separable complex Hilbert systems and $H_A\ge0$ a Hamiltonian with $\operatorname{Tr}e^{-\lambda H_A}<\infty$ for every $\lambda>0$. Let $F_H(E)$ be the supremum of von Neumann entropy in nats over all states of energy at most $E$, and let $\widehat F$ dominate it, with $\widehat F>0$, $\widehat F'>0$, $\widehat F''<0$ on positive arguments and $\widehat F(E)=o(E)$. For states $\rho,\sigma$ whose $A$-marginal energies are at most $E\ge E_0$, both QCMIs are finite. Write $h_2$ for binary entropy and $g(x)=(1+x)\log(1+x)-x\log x$. If $\frac12\|\rho-\sigma\|_1\le\varepsilon\in(0,1]$, then, for $0<t\le1/(2\varepsilon)$,
--
--   $$|I(A:B|C)_\rho-I(A:B|C)_\sigma|\le 2\varepsilon(2t+r_\varepsilon(t))\widehat F(E/(\varepsilon t))+2g(\varepsilon r_\varepsilon(t))+4h_2(\varepsilon t),\qquad r_\varepsilon(t)=\frac{1+t/2}{1-\varepsilon t}.$$
--
--   One may replace $r_\varepsilon$ by $r_1$ when $t<1$. Zero distance gives equality without division by zero. This gives energy-constrained QCMI continuity for arbitrary conditioning and reference systems.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 14, Proposition 2, (35): optimized energy-constrained QCMI continuity; original seed

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

/-- Proposition 2, PDF pp.13–15, (35). Finiteness is concluded from energy,
not assumed. Printed: r_epsilon(t)<=r_1(t) throughout 0<t<=1/(2epsilon).
Changed: only the optional r_1 replacement requires t<1. Why: 1-t
vanishes at t=1 and is negative for t>1; the original r_epsilon bound
retains its full domain. At distance zero the states have equal QCMI,
without evaluating E/(epsilon t). -/
theorem propositionTwo {I J K : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (e : I → ℝ≥0) (he : SpectralGibbsCondition e) (F : ℝ → ℝ) (hF : EntropyMajorant e F)
    (E : ℝ) (hE : ground e ≤ E) (rho sigma : State (I × (J × K)))
    (hrho : coefficientEnergy e (partialTraceSecond rho.coefficients) ≤ ENNReal.ofReal E)
    (hsigma : coefficientEnergy e (partialTraceSecond sigma.coefficients) ≤ ENNReal.ofReal E) :
    qcmi rho.coefficients < ⊤ ∧ qcmi sigma.coefficients < ⊤ ∧
    (extendedHalfTraceDistance rho.coefficients sigma.coefficients = 0 →
      qcmi rho.coefficients = qcmi sigma.coefficients) ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      extendedHalfTraceDistance rho.coefficients sigma.coefficients ≤ ENNReal.ofReal epsilon →
      ∀ t : ℝ, 0 < t → t ≤ 1 / (2 * epsilon) →
        |(qcmi rho.coefficients).toReal - (qcmi sigma.coefficients).toReal| ≤
          qcmiBoundWith F E epsilon t (continuityRatio epsilon t) ∧
        (t < 1 → |(qcmi rho.coefficients).toReal - (qcmi sigma.coefficients).toReal| ≤
          qcmiBoundWith F E epsilon t (continuityRatio 1 t)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
