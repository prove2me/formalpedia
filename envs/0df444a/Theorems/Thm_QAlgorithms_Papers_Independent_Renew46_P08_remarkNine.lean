-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkNine
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkNine
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:04:22.69617+00:00
-- url     : https://prove2.me/theorems/eacc231d-159e-4579-b729-37bf876c4887
-- title:
--   Remark 9: D0 and DK variants
-- statement:
--   For countable ensembles, $D_*\le D_0$ and $D_*\le D_K$. Under the Gibbs Hamiltonian and entropy-majorant assumptions of Proposition 7 and average energies at most $E\ge E_0$, the Holevo quantities are finite. For either $D=D_0$ or $D=D_K$, $D(\mu,\nu)\le\varepsilon\in(0,1]$ gives, for $0<t\le1/(2\varepsilon)$,
--
--   $$|\chi(\mu)-\chi(\nu)|\le\varepsilon(2t+r_\varepsilon(t))\widehat F(E/(\varepsilon t))+2g(\varepsilon r_\varepsilon(t))+2h_2(\varepsilon t).$$
--
--   The replacement by $r_1$ requires $t<1$, and zero distance gives equality. These are distance substitutions, with no converse modulus or equality of metrics. For a full positive-frequency ell-mode oscillator, both distances also give (69) explicitly: the main term is epsilon(2t+r_epsilon(t)) [Fhat_ell,omega(E)-ell log(epsilon t)], with additive terms 2g(epsilon r_epsilon(t))+2h2(epsilon t). This branch assumes only the oscillator data and the two average-energy budgets, and concludes finite Holevo values before taking their real difference. Zero distance is handled by equality.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 28, Remark 9: D0 and DK variants

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

/-- Remark 9, PDF p.28: both (68) and the oscillator bound (69) remain
valid with D0 or DK. The oscillator clause uses actual full Fock levels and
average-energy constraints, without a separate majorant hypothesis.
Printed: the optional r_1 comparison has no t<1 qualification. Changed:
the generic r_1 clause requires t<1. Why: its denominator is 1-t.
The sharpness construction remains part of the separately deferred
Proposition 7; this remark records its metric substitutions for the bounds. -/
theorem remarkNine :
    (∀ {I : Type} [Countable I] [Nonempty I]
    (e : I → ℝ≥0) (he : SpectralGibbsCondition e) (F : ℝ → ℝ) (hF : EntropyMajorant e F)
    (E : ℝ) (hE : ground e ≤ E) (mu nu : CountableStateEnsemble I)
    (hmu : coefficientEnergy e (countableAverage mu) ≤ ENNReal.ofReal E)
    (hnu : coefficientEnergy e (countableAverage nu) ≤ ENNReal.ofReal E),
    distanceStar mu nu ≤ distance0 mu nu ∧ distanceStar mu nu ≤ distanceK mu nu ∧
    countableHolevo mu < ⊤ ∧ countableHolevo nu < ⊤ ∧
    ∀ D ∈ ({distance0, distanceK} : Set (CountableStateEnsemble I → CountableStateEnsemble I → ℝ≥0∞)),
      (D mu nu = 0 → countableHolevo mu = countableHolevo nu) ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → D mu nu ≤ ENNReal.ofReal epsilon →
        ∀ t : ℝ, 0 < t → t ≤ 1/(2*epsilon) →
          |(countableHolevo mu).toReal - (countableHolevo nu).toReal| ≤
            holevoBoundWith F E epsilon t (continuityRatio epsilon t) ∧
          (t < 1 → |(countableHolevo mu).toReal - (countableHolevo nu).toReal| ≤
            holevoBoundWith F E epsilon t (continuityRatio 1 t))) ∧
    (∀ (ell : ℕ), 0 < ell → ∀ (hbar : ℝ), 0 < hbar →
      ∀ omega : Fin ell → ℝ, (∀ i, 0 < omega i) →
      ∀ mu nu : CountableStateEnsemble (Fin ell → ℕ),
        ∀ E : ℝ, oscillatorGround hbar omega ≤ E →
          coefficientEnergy (oscillatorLevels hbar omega) (countableAverage mu) ≤ ENNReal.ofReal E →
          coefficientEnergy (oscillatorLevels hbar omega) (countableAverage nu) ≤ ENNReal.ofReal E →
          countableHolevo mu < ⊤ ∧ countableHolevo nu < ⊤ ∧
          ∀ D ∈ ({distance0, distanceK} : Set
            (CountableStateEnsemble (Fin ell → ℕ) → CountableStateEnsemble (Fin ell → ℕ) → ℝ≥0∞)),
            (D mu nu = 0 → countableHolevo mu = countableHolevo nu) ∧
            ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → D mu nu ≤ ENNReal.ofReal epsilon →
              ∀ t : ℝ, 0 < t → t ≤ 1/(2*epsilon) →
                |(countableHolevo mu).toReal - (countableHolevo nu).toReal| ≤
                  oscillatorMain 1 hbar omega E epsilon t +
                    2 * g (epsilon * continuityRatio epsilon t) +
                    2 * Real.binEntropy (epsilon*t)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
