-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_pure_ensemble_tradeoff
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.pure_ensemble_tradeoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:38:36.784913+00:00
-- url     : https://prove2.me/theorems/141aff6d-3a23-4b85-9e83-7b5988b70c1f
-- title:
--   Theorem 11: pure-ensemble RSP trade-off
-- statement:
--   Let $\mathcal E=\{p_i,|\psi_i\rangle\}_{i=1}^m$ be a finite ensemble on a fixed space $\mathbb C^d$, $d\ge1$, with nonnegative probabilities summing to one and normalized vectors. Repeated targets and zero probabilities are allowed. On length-$n$ blocks the source states and probabilities are products. Let $E^*(R)$ be the infimum of nonnegative ebit rates achievable at cbit rate $R\ge0$, where every positive error and rate slack precede a blocklength threshold, every larger blocklength admits one one-way code, and fidelity is the global ensemble average. Then
--
--   $$E^*(R)=\min_{p(j|i)}\{I(A;B\mid C)_\omega:I(A;BC)_\omega\le R\},\qquad
--   \omega=\sum_{i,j}p_i p(j|i)|i\rangle\langle i|^A\otimes\psi_i^B\otimes|j\rangle\langle j|^C.$$
--
--   The auxiliary alphabet is finite but arbitrary. For these pure targets $I(A;B\mid C)=S(B\mid C)$. At every feasible rate the information minimum is attained and the resulting operational rate pair is achievable; infeasible rates have value $+\infty$. All entropies are in bits. This identifies the complete one-way pure-ensemble trade-off.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 6, Theorem 11: pure-ensemble RSP trade-off

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

/-- Theorem 11, PDF pp.6–7. The operational curve equals the minimum over equation (5),
including the attainment assertion at feasible rates. Repeated targets are allowed. -/
theorem pure_ensemble_tradeoff {d : ℕ} (hd : 0 < d) (E : PureEnsemble (Fin d))
    (R : ℝ) (hR : 0 ≤ R) :
    pureOperational E R = rspSingleLetter E.weight (fun i => pureDensity (E.vector i)) R ∧
    rspMinimumAttained E.weight (fun i => pureDensity (E.vector i)) R ∧
    (pureOperational E R ≠ ⊤ → RSPPureAchievable E R (pureOperational E R).toReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
