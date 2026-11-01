-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_entangled_ensemble_tradeoff
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.entangled_ensemble_tradeoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:41:33.639814+00:00
-- url     : https://prove2.me/theorems/e45ad276-b611-4468-a059-d2be1be63fdd
-- title:
--   Theorem 18: entangled ensemble trade-off
-- statement:
--   Let $\mathcal E=\{p_i,|\phi_i\rangle^{AB}\}$ be a finite normalized pure bipartite ensemble in fixed positive dimensions, and let $R\ge0$. Define its operational ebit curve using one-way input-dependent Alice CP instruments, message-dependent arbitrary CPTP Bob decoders, iid product blocks, global average fidelity, and both positive rate slacks and errors before every sufficiently large blocklength. Then
--
--   $$E^*(R)=\min_{p(j|i)}\{S(B\mid C)_\omega:I(X;BC)_\omega\le R\},\qquad
--   \omega=\sum_{i,j}p_i p(j|i)|i\rangle\langle i|^X\otimes\phi_i^{AB}\otimes|j\rangle\langle j|^C.$$
--
--   The classical auxiliary is finite but arbitrary. At feasible rates the minimum is attained and its rate pair is achievable; an infeasible rate has value $+\infty$. The cost $S(B\mid C)$ averages receiver conditional entropies. In particular it is not replaced by $I(X;B\mid C)$. Although the operational target preserves Alice's purification, the information curve depends only on the receiver marginal ensemble.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 10, Theorem 18: entangled ensemble trade-off

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

/-- Theorem 18, PDF pp.10–11: minimise S(B|C), not I(X;B|C), over all finite stochastic
auxiliaries subject to I(X;BC) ≤ R. The operational target includes Alice's purification. -/
theorem entangled_ensemble_tradeoff {m a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : BipartiteEnsemble m a b) (R : ℝ) (hR : 0 ≤ R) :
    bipOperational E R = rspSingleLetter E.prob (bobStates E) R ∧
    rspMinimumAttained E.prob (bobStates E) R ∧
    (bipOperational E R ≠ ⊤ → BipartiteAchievable E R (bipOperational E R).toReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
