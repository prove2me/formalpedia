-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P43_pureEnsemble_coherentInformation_identity
-- name    : QAlgorithms.Papers.Independent.Gap48.P43.pureEnsemble_coherentInformation_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:36:00.794529+00:00
-- url     : https://prove2.me/theorems/b4bb6814-df50-4013-826a-313503fd6056
-- title:
--   Pure-ensemble Holevo difference equals coherent information
-- statement:
--   Let $\{p_k,\rho_k\}$ be a finite or countable probability ensemble of normalized density operators on $Q$, with every signal of positive probability pure. Let the complete environment $E$ begin in one normalized pure state and let $U$ be one fixed unitary on $Q\otimes E$. Compute $\bar\rho=\sum_kp_k\rho_k$ and the conditional and average outputs for Bob and Eve by the two partial traces of this same evolution.
--
--   For $H\in\{B,E\}$, let $\chi_H=S(\rho'_H)-\sum_kp_kS(\rho'_{H,k})$, where $S$ is von Neumann entropy in bits with zero eigenvalues contributing zero. Assume both average output entropies and both weighted conditional entropy sums are finite. Define $I^Q=S(\rho'_B)-S(\rho'_E)$. Then
--
--   $$
--   I^Q=\chi_B-\chi_E.
--   $$
--
--   The identity relates the classical Holevo quantities of one pure signal ensemble to coherent information of its average input. Neither orthogonality of the inputs, finite-dimensional registers, finite input entropy, nor positivity of coherent information is required. Equality of the conditional entropies is a consequence of the model, not a hypothesis.
-- source:
--   Quantum privacy and quantum coherence, arXiv:quant-ph/9709058v2, PDF p. 4, Equation (11): pure-ensemble Holevo difference equals coherent information

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P43

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Gap48.P43

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble boundedConjugation traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (boundedOperator operatorCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits)

open QAlgorithms.Papers.Independent.Frontier30.P10 (HilbertPOVM)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Schumacher--Westmoreland, quant-ph/9709058v2, PDF p.4, equation (11).
For pure active inputs, the output Holevo difference equals coherent
information of the computed average input. Joint purity and equality of
conditional output entropies are consequences, never hypotheses. -/
theorem pureEnsemble_coherentInformation_identity {Q E : Type}
    (d : PureDilation Q E) (a : CountableStateEnsemble Q)
    (hpure : ActivePure a)
    (hBob : FiniteOutputEntropies a (bobOutput d))
    (hEve : FiniteOutputEntropies a (eveOutput d)) :
    (spectralEntropyBits (bobOutput d (averageInput a))).toReal -
      (spectralEntropyBits (eveOutput d (averageInput a))).toReal =
      holevoBits a (bobOutput d) - holevoBits a (eveOutput d) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P43

end
