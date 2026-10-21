-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_propositionNine
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.propositionNine
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:07:17.592978+00:00
-- url     : https://prove2.me/theorems/c916d58e-3650-4cfa-b475-e7aac7007d0c
-- title:
--   Proposition 9, (75)–(76): generalized-ensemble continuity bounds
-- statement:
--   For generalized ensembles $\mu,\nu$, let $\varepsilon=D_K(\mu,\nu)$, where $D_K$ minimizes the integrated half trace norm over all probability couplings. If the system has finite dimension $d$, their Holevo quantities are finite and
--
--   $$|\chi(\mu)-\chi(\nu)|\le\varepsilon\log d+2g(\varepsilon),$$
--
--   with $g(\varepsilon)$ replacing $2g(\varepsilon)$ when the barycenters agree. For a Gibbs Hamiltonian and a regular entropy majorant $\widehat F$, average energies at most $E\ge E_0$ instead give, at positive $\varepsilon$ and $0<t\le1/(2\varepsilon)$,
--
--   $$|\chi(\mu)-\chi(\nu)|\le\varepsilon(2t+r_\varepsilon(t))\widehat F(E/(\varepsilon t))+2g(\varepsilon r_\varepsilon(t))+2h_2(\varepsilon t).$$
--
--   Zero distance gives equality. For a positive-frequency full Fock oscillator, the majorant term is replaced by $\widehat F_{\ell,\omega}(E)-\ell\log(\varepsilon t)$, as in (69). This extends the bounds to non-atomic laws without asserting an extension of $D_*$.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 31, Proposition 9, (75)–(76): generalized-ensemble continuity bounds

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

/-- Proposition 9, PDF pp.30–32, (75)–(76): generalized DK bounds, finite
output values established before all real differences, equality at DK=0,
the equal-barycenter refinement, and the oscillator specialization (69).
The oscillator clause is separately quantified over its full Fock space. -/
theorem propositionNine :
    (∀ (I : Type) [Countable I] [Nonempty I] (mu nu : GeneralizedEnsemble I),
      let epsilon := (generalizedK mu nu).toReal
      (Finite I → ensembleHolevo id mu < ⊤ ∧ ensembleHolevo id nu < ⊤ ∧
        |(ensembleHolevo id mu).toReal - (ensembleHolevo id nu).toReal| ≤
          epsilon * Real.log (Nat.card I) + 2 * g epsilon ∧
        (averageCoefficients mu = averageCoefficients nu →
          |(ensembleHolevo id mu).toReal - (ensembleHolevo id nu).toReal| ≤
            epsilon * Real.log (Nat.card I) + g epsilon)) ∧
      (∀ (e : I → ℝ≥0) (F : ℝ → ℝ), SpectralGibbsCondition e → EntropyMajorant e F →
        ∀ E : ℝ, ground e ≤ E →
          coefficientEnergy e (averageCoefficients mu) ≤ ENNReal.ofReal E →
          coefficientEnergy e (averageCoefficients nu) ≤ ENNReal.ofReal E →
          ensembleHolevo id mu < ⊤ ∧ ensembleHolevo id nu < ⊤ ∧
          (generalizedK mu nu = 0 → ensembleHolevo id mu = ensembleHolevo id nu) ∧
          (0 < epsilon → ∀ t : ℝ, 0 < t → t ≤ 1/(2*epsilon) →
            |(ensembleHolevo id mu).toReal - (ensembleHolevo id nu).toReal| ≤
              holevoBoundWith F E epsilon t (continuityRatio epsilon t)))) ∧
    (∀ (ell : ℕ), 0 < ell → ∀ (hbar : ℝ), 0 < hbar →
      ∀ omega : Fin ell → ℝ, (∀ i, 0 < omega i) →
      ∀ mu nu : GeneralizedEnsemble (Fin ell → ℕ),
        ∀ E : ℝ, oscillatorGround hbar omega ≤ E →
          coefficientEnergy (oscillatorLevels hbar omega) (averageCoefficients mu) ≤ ENNReal.ofReal E →
          coefficientEnergy (oscillatorLevels hbar omega) (averageCoefficients nu) ≤ ENNReal.ofReal E →
          let epsilon := (generalizedK mu nu).toReal
          ensembleHolevo id mu < ⊤ ∧ ensembleHolevo id nu < ⊤ ∧
          (generalizedK mu nu = 0 → ensembleHolevo id mu = ensembleHolevo id nu) ∧
          (0 < epsilon → ∀ t : ℝ, 0 < t → t ≤ 1/(2*epsilon) →
            |(ensembleHolevo id mu).toReal - (ensembleHolevo id nu).toReal| ≤
              oscillatorMain 1 hbar omega E epsilon t +
                2 * g (epsilon * continuityRatio epsilon t) +
                2 * Real.binEntropy (epsilon*t))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
