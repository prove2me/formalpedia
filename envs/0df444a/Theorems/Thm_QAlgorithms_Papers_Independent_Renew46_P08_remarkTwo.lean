-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkTwo
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkTwo
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:49:44.728813+00:00
-- url     : https://prove2.me/theorems/be7edd9b-3523-4093-9b13-f3d7fdd7fa4d
-- title:
--   Remark 2: Winter change of variables
-- statement:
--   Under the Hamiltonian, entropy-majorant and energy assumptions of Proposition 2, suppose $\frac12\|\rho-\sigma\|_1\le\varepsilon$ with $\varepsilon>0$. For $\varepsilon<\varepsilon'\le1$, put $\delta_{\varepsilon'}=(\varepsilon'-\varepsilon)/(\varepsilon'+1/2)$ and assume $\delta_{\varepsilon'}\le1/2$. Then both QCMIs are finite and
--
--   $$|I(A:B|C)_\rho-I(A:B|C)_\sigma|\le2(2\delta_{\varepsilon'}+\varepsilon')\widehat F(E/\delta_{\varepsilon'})+2g(\varepsilon')+4h_2(\delta_{\varepsilon'}).$$
--
--   The substitution satisfies $\varepsilon'=\varepsilon r_\varepsilon(\delta_{\varepsilon'}/\varepsilon)$. The symbol $\delta_{\varepsilon'}$ is an indexed parameter, not a product. This is the source's restricted Winter parametrization.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 14, Remark 2: Winter change of variables

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

/-- Remark 2, PDF p.14: delta indexed by epsilon_prime, rather than a product.
The equality epsilon_prime=epsilon*r_epsilon(delta/epsilon) is also recorded. -/
theorem remarkTwo {I J K : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (e : I → ℝ≥0) (he : SpectralGibbsCondition e) (F : ℝ → ℝ) (hF : EntropyMajorant e F)
    (E : ℝ) (hE : ground e ≤ E) (rho sigma : State (I × (J × K)))
    (hrho : coefficientEnergy e (partialTraceSecond rho.coefficients) ≤ ENNReal.ofReal E)
    (hsigma : coefficientEnergy e (partialTraceSecond sigma.coefficients) ≤ ENNReal.ofReal E)
    (epsilon epsilonPrime : ℝ) (heps : 0 < epsilon) (hprime : epsilon < epsilonPrime)
    (hprimeone : epsilonPrime ≤ 1)
    (hd : (epsilonPrime - epsilon) / (epsilonPrime + 1/2) ≤ 1/2)
    (hdist : extendedHalfTraceDistance rho.coefficients sigma.coefficients ≤ ENNReal.ofReal epsilon) :
    let delta := (epsilonPrime - epsilon) / (epsilonPrime + 1/2)
    qcmi rho.coefficients < ⊤ ∧ qcmi sigma.coefficients < ⊤ ∧
    epsilonPrime = epsilon * continuityRatio epsilon (delta / epsilon) ∧
    |(qcmi rho.coefficients).toReal - (qcmi sigma.coefficients).toReal| ≤
      2 * (2 * delta + epsilonPrime) * F (E / delta) +
        2 * g epsilonPrime + 4 * Real.binEntropy delta := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
