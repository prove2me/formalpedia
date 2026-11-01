-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_optimal_cbit_entangled_preparation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.optimal_cbit_entangled_preparation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:39:19.670986+00:00
-- url     : https://prove2.me/theorems/5dacbd8c-7401-4574-b719-92bf391f94c8
-- title:
--   Proposition 15: optimal-cbit entangled ensemble preparation
-- statement:
--   Let $\mathcal E=\{p_i,|\phi_i\rangle^{AB}\}$ be a finite probability ensemble of normalized bipartite vectors in fixed positive dimensions. Write $\rho_i^B=\operatorname{Tr}_A\phi_i$ and $\bar\rho^B=\sum_i p_i\rho_i^B$. There are one-way entangled preparation codes achieving
--
--   $$R=\chi(\{p_i,\rho_i^B\})=S(\bar\rho^B)-\sum_i p_iS(\rho_i^B),\qquad E=S(\bar\rho^B).$$
--
--   Achievability means that, for every positive error and rate slack, every sufficiently large blocklength admits one code with the stated cbit and ebit rates up to that slack and global average overlap at least one minus the error. Alice uses input-dependent CP instruments; Bob uses fixed message-dependent CPTP decoders. The joint output approximates the chosen product purification, including Alice's share. This is the optimal-cbit endpoint; its ebit rate is entropy of the average, not average entropy.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 9, Proposition 15: optimal-cbit entangled ensemble preparation

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

/-- Proposition 15, PDF pp.9–10: the optimal-cbit achievable corner retains Alice's
purification and consumes entropy of the AVERAGE Bob state in ebits. -/
theorem optimal_cbit_entangled_preparation {m a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : BipartiteEnsemble m a b) :
    BipartiteAchievable E (bobHolevo E) (bobAverageEntropy E) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
