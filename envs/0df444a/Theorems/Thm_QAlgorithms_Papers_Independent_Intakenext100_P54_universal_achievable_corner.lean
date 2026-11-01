-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_universal_achievable_corner
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.universal_achievable_corner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:37:21.181853+00:00
-- url     : https://prove2.me/theorems/b9f24397-24ad-4d07-adf1-0ea862674c64
-- title:
--   Corollary 6: universal achievable corner
-- statement:
--   For every error $\varepsilon>0$ and rate slack $\delta>0$, there is $D_0\ge2$ such that every $D\ge D_0$ admits a one-way protocol, chosen before its arbitrary normalized pure target in $\mathbb C^D$, with shared maximally entangled rank $D$ resource, exact conditional successful output, and a common success/failure flag, satisfying
--
--   $$\Pr\{\mathrm{failure}\}\le\varepsilon,\qquad \log_2K\le(1+\delta)\log_2D.$$
--
--   Here $K$ counts every possible forward message, including failure; Bob uses a fixed CPTP decoder for each message. The entanglement cost is $\log_2D$. Thus one cbit and one ebit per qubit are simultaneously achievable asymptotically for universal probabilistic exact preparation.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 4, Corollary 6: universal achievable corner

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Corollary 6, PDF p.4. The error and rate slack precede the dimension threshold and code;
the code precedes every arbitrary pure target. The failure outcome is charged. -/
theorem universal_achievable_corner :
    ∀ eps : ℝ, 0 < eps → ∀ delta : ℝ, 0 < delta →
      ∃ Dzero : ℕ, 2 ≤ Dzero ∧ ∀ D ≥ Dzero,
        ∃ P : RSPCode (RSPVector (Fin D)) (Fin D),
          P.S = D ∧ Real.logb 2 P.K ≤ (1 + delta) * Real.logb 2 D ∧
          P.ExactWithError eps := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
