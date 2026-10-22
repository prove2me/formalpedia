-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P43_pureDecomposition_holevoDifference_independent
-- name    : QAlgorithms.Papers.Independent.Gap48.P43.pureDecomposition_holevoDifference_independent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:36:45.12036+00:00
-- url     : https://prove2.me/theorems/d95c329c-5eca-4503-8e88-ba41c604ced7
-- title:
--   The Holevo difference is independent of the pure decomposition
-- statement:
--   Fix a unitary interaction of a quantum register $Q$ with one complete environment $E$ in a normalized pure initial state. Let $\mathcal A=\{p_k,\rho_k\}$ and $\mathcal B=\{q_l,\sigma_l\}$ be finite or countable probability ensembles of normalized input states, pure whenever their probability is nonzero. Their computed average inputs are equal:
--
--   $$
--   \sum_kp_k\rho_k=\sum_lq_l\sigma_l.
--   $$
--
--   For each ensemble $\mathcal C$ and each output $H\in\{B,E\}$, compute the conditional and average output states from that fixed interaction and put $\chi_H(\mathcal C)=S(\bar\rho'_H)-\sum_j r_jS(\rho'_{H,j})$, with entropies in bits. Assume the average output entropies and the weighted conditional entropy sums appearing in these differences are finite. Then
--
--   $$
--   \chi_B(\mathcal A)-\chi_E(\mathcal A)
--   =\chi_B(\mathcal B)-\chi_E(\mathcal B).
--   $$
--
--   Thus the difference depends only on the average density operator. The assertion permits different alphabets and probabilities, repeated and nonorthogonal signals, and channels for which one or both individual Holevo quantities are constant.
-- source:
--   Quantum privacy and quantum coherence, arXiv:quant-ph/9709058v2, PDF p. 5, Unnumbered result after (12): pure-decomposition independence

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

/-- Schumacher--Westmoreland, quant-ph/9709058v2, PDF p.5, paragraph after (12).
Two pure discrete decompositions with the same computed average have the same
Holevo difference. No nonconstant dependence of either individual chi is asserted. -/
theorem pureDecomposition_holevoDifference_independent {Q E : Type}
    (d : PureDilation Q E) (a b : CountableStateEnsemble Q)
    (ha : ActivePure a) (hb : ActivePure b)
    (haverage : averageInput a = averageInput b)
    (haBob : FiniteOutputEntropies a (bobOutput d))
    (haEve : FiniteOutputEntropies a (eveOutput d))
    (hbBob : FiniteOutputEntropies b (bobOutput d))
    (hbEve : FiniteOutputEntropies b (eveOutput d)) :
    holevoBits a (bobOutput d) - holevoBits a (eveOutput d) =
      holevoBits b (bobOutput d) - holevoBits b (eveOutput d) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P43

end
