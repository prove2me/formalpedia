-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_cq_reverse_shannon_application
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.cq_reverse_shannon_application
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:42:50.175342+00:00
-- url     : https://prove2.me/theorems/0d6363e0-2643-41d9-a6ae-85747b840c77
-- title:
--   Section VI.C: cq quantum reverse Shannon application
-- statement:
--   For a fixed finite ensemble $\{p_i,|\phi_i\rangle^{AB}\}$ of normalized pure bipartite states, let $\rho_i^B$ be the receiver marginals and $\bar\rho^B=\sum_i p_i\rho_i^B$. For every positive error and rate slack, all sufficiently large blocklengths admit one code simultaneously approximating the chosen product purifications in global average overlap and their receiver marginals in average squared Uhlmann fidelity, with
--
--   $$R=\chi(\{p_i,\rho_i^B\}),\qquad E=S(\bar\rho^B).$$
--
--   Both average fidelities are at least one minus the requested error, and both support rates are bounded by the displayed rates plus the requested slack. Alice's share is discarded only when evaluating the second fidelity. This gives the stated cq reverse Shannon application for the fixed ensemble law, without a channel diamond-norm assertion.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 13, Section VI.C: cq quantum reverse Shannon application

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

/-- Section VI.C, PDF p.13: the preparation scheme simultaneously approximates the chosen
purifications and the receiver's mixed-state ensemble at Holevo cbit rate. This is a fixed-law
average-fidelity assertion, not a diamond-norm simulation claim. -/
theorem cq_reverse_shannon_application {m a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : BipartiteEnsemble m a b) :
    ∀ eps : ℝ, 0 < eps → ∀ delta : ℝ, 0 < delta →
      ∃ nzero : ℕ, 0 < nzero ∧ ∀ n ≥ nzero,
        ∃ P : BipartiteCode (Fin n → Fin m) (Fin n → Fin a) (Fin n → Fin b),
          1 - eps ≤ bipAverage E n P ∧ 1 - eps ≤ marginalAverageFidelity E n P ∧
          Real.logb 2 P.K / n ≤ bobHolevo E + delta ∧
          Real.logb 2 P.S / n ≤ bobAverageEntropy E + delta := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
