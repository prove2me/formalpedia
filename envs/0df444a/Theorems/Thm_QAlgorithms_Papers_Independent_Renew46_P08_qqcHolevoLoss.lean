-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_qqcHolevoLoss
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.qqcHolevoLoss
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:46:52.976667+00:00
-- url     : https://prove2.me/theorems/47f54838-908e-41c2-81a1-4fdfa8139712
-- title:
--   Unnumbered Holevo-loss identity after Corollary 2
-- statement:
--   For a finite or countable ensemble $\{p_i,\rho^i_{AC}\}$, form the actual qqc state $\rho_{ABC}=\sum_i p_i\rho^i_{AC}\otimes|i\rangle\langle i|_B$. Let $\chi_{AC}$ and $\chi_C$ denote its ensemble Holevo quantities, defined by sums of relative entropies to the respective averages. Then
--
--   $$\chi_{AC}=I(A:B|C)_\rho+\chi_C.$$
--
--   This extended nonnegative identity remains meaningful when quantities are infinite. When the Holevo quantities are finite, it is precisely the source's Holevo-loss difference formula.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 12, Unnumbered Holevo-loss identity after Corollary 2

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

/-- Unnumbered identity after Corollary 2, PDF p.12. Extended additive form
avoids infinity minus infinity and includes countably many labels. -/
theorem qqcHolevoLoss {I K : Type} [Countable I] [Countable K]
    [Nonempty I] [Nonempty K] (mu : CountableStateEnsemble (I × K)) :
    countableHolevo mu = qcmi (qqcState mu) + marginalChi mu := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
