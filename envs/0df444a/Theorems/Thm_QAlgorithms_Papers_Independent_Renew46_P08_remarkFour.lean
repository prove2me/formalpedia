-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkFour
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkFour
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:51:02.770053+00:00
-- url     : https://prove2.me/theorems/b4beb0d4-b6dd-4844-909d-0ddf100db13d
-- title:
--   Remark 4: QCMI uniform continuity under energy bound
-- statement:
--   For a nonnegative Gibbs Hamiltonian $H_A$ and a regular sublinear entropy majorant $\widehat F$ as in Proposition 2, fix $E>E_0$. Then $x\widehat F(E/x)\to0$ as $x\downarrow0$, and QCMI is finite throughout the set $\mathcal C_{H_A,E}$ of tripartite states with $A$-marginal energy at most $E$. Moreover,
--
--   $$\forall\eta>0\ \exists\delta>0\ \forall\rho,\sigma\in\mathcal C_{H_A,E},\quad \tfrac12\|\rho-\sigma\|_1<\delta\ \Longrightarrow\ |I(A:B|C)_\rho-I(A:B|C)_\sigma|<\eta.$$
--
--   The choice of $\delta$ is uniform over the entire energy-constrained state set, with arbitrary systems $B,C$.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 14, Remark 4: QCMI uniform continuity under energy bound

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

/-- Remark 4, PDF p.14: uniform trace-distance continuity on the entire
coefficientEnergy-constrained tripartite state set, arbitrary B and C. -/
theorem remarkFour {I J K : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (e : I → ℝ≥0) (he : SpectralGibbsCondition e) (F : ℝ → ℝ) (hF : EntropyMajorant e F)
    (E : ℝ) (hE : ground e < E) :
    Tendsto (fun x : ℝ => x * F (E/x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ rho : State (I × (J × K)),
      coefficientEnergy e (partialTraceSecond rho.coefficients) ≤ ENNReal.ofReal E → qcmi rho.coefficients < ⊤) ∧
    (∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ rho sigma : State (I × (J × K)),
        coefficientEnergy e (partialTraceSecond rho.coefficients) ≤ ENNReal.ofReal E →
        coefficientEnergy e (partialTraceSecond sigma.coefficients) ≤ ENNReal.ofReal E →
        extendedHalfTraceDistance rho.coefficients sigma.coefficients < ENNReal.ofReal delta →
        |(qcmi rho.coefficients).toReal - (qcmi sigma.coefficients).toReal| < eta) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
