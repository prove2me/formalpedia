-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P43_fixedStrategy_guaranteedPrivacy_lowerBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P43.fixedStrategy_guaranteedPrivacy_lowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:35:15.609311+00:00
-- url     : https://prove2.me/theorems/c0c7dcfd-087c-4d38-ab63-b87b8393f541
-- title:
--   Fixed-strategy guaranteed privacy is bounded below by Bob information minus environment Holevo information
-- statement:
--   Fix a quantum register $Q$, its complete environment $E$, a normalized pure initial environment, and a unitary $U$ on $Q\otimes E$. Fix a finite or countable ensemble $\{p_k,\rho_k\}$ of normalized input density operators, with $p_k\ge0$ and $\sum_kp_k=1$, and one decoding POVM for Bob, with arbitrary measurable outcomes. Let $H_B<\infty$ be the classical mutual information, in bits, between the signal label and Bob's outcome, computed from its Born law. The two output ensembles are the partial traces of $U(\rho_k\otimes|0\rangle\langle0|)U^\dagger$, and their average is computed from $\bar\rho=\sum_kp_k\rho_k$.
--
--   Write $\chi_E=S(\rho'_E)-\sum_kp_kS(\rho'_{E,k})$, using ordinary von Neumann entropy in bits. Suppose the average environment entropy and the weighted conditional environment entropy are finite. Let $P_G=\inf_M[H_B-I(K:Y_M)]$, where $M$ ranges over every POVM of the complete environment, on every measurable outcome space, and $I(K:Y_M)$ is its Born-law classical mutual information in bits. Then
--
--   $$
--   P_G\ge H_B-\chi_E.
--   $$
--
--   This is a guarantee for a fixed Alice ensemble and Bob decoder. The infimum includes Eve's classical processing and access to any subsystem through full-environment POVMs, and $P_G$ is allowed to be negative. It does not invoke a coding-rate optimum.
-- source:
--   Quantum privacy and quantum coherence, arXiv:quant-ph/9709058v2, PDF p. 4, Equation (8): fixed-strategy guaranteed privacy lower bound

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

/-- Schumacher--Westmoreland, quant-ph/9709058v2, PDF p.4, equation (8).
For one fixed ensemble and Bob measurement, guaranteed privacy is at least
Bob's actual classical information minus the complete-environment Holevo
quantity. Neither the Holevo bound nor an entropy equality is a premise. -/
theorem fixedStrategy_guaranteedPrivacy_lowerBound {Q E X : Type} [MeasurableSpace X]
    (d : PureDilation Q E) (a : CountableStateEnsemble Q)
    (B : HilbertPOVM (Hilbert Q) X)
    (hBob : measuredInformation a (bobOutput d) B < ⊤)
    (hEve : FiniteOutputEntropies a (eveOutput d)) :
    (((measuredInformation a (bobOutput d) B).toReal -
      holevoBits a (eveOutput d) : ℝ) : EReal) ≤
      guaranteedPrivacy a d (measuredInformation a (bobOutput d) B).toReal := by sorry

end QAlgorithms.Papers.Independent.Gap48.P43

end
