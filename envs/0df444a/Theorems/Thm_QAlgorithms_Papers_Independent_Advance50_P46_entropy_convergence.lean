-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_entropy_convergence
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.entropy_convergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:07:36.060344+00:00
-- url     : https://prove2.me/theorems/5dc441ef-ea25-4978-ab97-338e4f3feb07
-- title:
--   Proposition [Entropy convergence], parts (1)–(2)
-- statement:
--   Let $H\ge0$ satisfy the Gibbs hypothesis and have the ordered spectral-pair ratio limit $\xi>1$, with $\eta=(\xi-1)^{-1}$. Write $F_H(x)=\sup_{\operatorname{Tr}(H\tau)\le x}S(\tau)$ for its maximum-entropy envelope. Above the ground energy this is $S(\gamma(x))$. Let $\rho,\sigma$ have energies at most $E$ and $\tfrac12\|\rho-\sigma\|_1\le\varepsilon$, where $0<\varepsilon\le1$. Then their entropies are finite and
--
--   $$|S(\rho)-S(\sigma)|\le2\varepsilon F_H(E/\varepsilon)+h(\varepsilon).$$
--
--   For $\varepsilon<\varepsilon'\le1$ and $\delta=(\varepsilon'-\varepsilon)/(1+\varepsilon')$,
--
--   $$|S(\rho)-S(\sigma)|\le(\varepsilon'+2\delta)F_H(E/\delta)+h(\varepsilon')+h(\delta).$$
--
--   Here $h$ is binary entropy in nats. At high arguments $F_H(x)=\eta\log x(1+R_H(x))$ with the single Hamiltonian-specific remainder $R_H(x)\to0$. This gives both printed expansions while preserving the proof's exact Gibbs envelopes at finite error, including ground-energy endpoints. In the second expression the expansion requires $E/\delta\to\infty$.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 16, Proposition [Entropy convergence], parts (1)–(2)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

attribute [local instance] Classical.propDecidable Classical.decEq

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Proposition [Entropy convergence], PDF pp.16,42, parts (1)--(2). Exact Gibbs
maximum-entropy envelopes from the proof preserve all finite error parameters;
the common remainder supplies the printed high-argument expansions. No finite
value is assigned to an unspecified o(1), including at E/epsilon=1. -/
theorem entropy_convergence {I : Type} [Countable I] [Infinite I]
    (H : Spectral.Hamiltonian I) (hpos : ∀ i, 0 ≤ H.energy i) (hG : H.gibbs)
    (xi : ℝ) (hxi : HasPairRatio H xi) :
    ThermalAsymptotic H xi ∧
    ∀ (rho sigma : State I) (E epsilon : ℝ),
      H.meanEnergy rho ≤ (E : EReal) → H.meanEnergy sigma ≤ (E : EReal) →
      0 < epsilon → epsilon ≤ 1 →
      traceSize (rho.coefficients - sigma.coefficients) ≤ ENNReal.ofReal (2 * epsilon) →
      Spectral.homogeneousEntropy rho.coefficients < ⊤ ∧
      Spectral.homogeneousEntropy sigma.coefficients < ⊤ ∧
      (|((Spectral.homogeneousEntropy rho.coefficients).toReal) -
          ((Spectral.homogeneousEntropy sigma.coefficients).toReal)| ≤
        2 * epsilon * (thermalEnvelope H (E / epsilon)).toReal + Real.binEntropy epsilon) ∧
      (∀ epsilonPrime : ℝ, epsilon < epsilonPrime → epsilonPrime ≤ 1 →
        let delta := (epsilonPrime - epsilon) / (1 + epsilonPrime)
        |((Spectral.homogeneousEntropy rho.coefficients).toReal) -
          ((Spectral.homogeneousEntropy sigma.coefficients).toReal)| ≤
          (epsilonPrime + 2 * delta) * (thermalEnvelope H (E / delta)).toReal +
            Real.binEntropy epsilonPrime + Real.binEntropy delta) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
