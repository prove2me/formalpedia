-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_conditional_rank_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.conditional_rank_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:18:37.352005+00:00
-- url     : https://prove2.me/theorems/0aa211e7-ae75-4d4a-af51-41b94fb6518e
-- title:
--   5.11
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   For every one of the four conditional entropies in its DPI range, −log min(rankρ_A,rankρ_B)≤Hα(A|B)≤log rankρ_A; additionally Hα≥0 for separable normalized ρ_AB.
--
--   $$
--   -\log_2\min\{\operatorname{rank}\rho_A,\operatorname{rank}\rho_B\}\le H_\alpha(A|B)_\rho\le\log_2\operatorname{rank}\rho_A.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 86, 5.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#5.11
5.11, arXiv:1504.00233v5, PDF p.86. -/
theorem conditional_rank_bounds [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : IsDensityMatrix r)
    (sand up : Bool) (a : ENNReal) (ha : DPIOrder sand a) :
    (-Real.logb 2 (min (traceRight r).rank (traceLeft r).rank):EReal) ≤ paperConditional sand up a r ∧
    paperConditional sand up a r ≤ (Real.logb 2 (traceRight r).rank:EReal) ∧
    (paperSeparable r → 0 ≤ paperConditional sand up a r) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
