-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_first_two_parallel
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.first_two_parallel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:36:59.925921+00:00
-- url     : https://prove2.me/theorems/a0f8e956-421b-409f-bad5-95a4176381e4
-- title:
--   The first two training calls may be parallel for arbitrary N
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   For every $N\ge2$ and $d\ge2$, there is an admissible symmetric globally optimal learner whose first two source calls are parallel:
--
--   $$\exists R:\quad R\text{ globally minimizes }D\quad\text{and its first two calls share one parallel preparation}.$$
--
--   Every later source call obeys the ordinary causal recursion and may depend on earlier classical outcomes. This is the general positive parallelization result asserted in the conclusion; it does not extrapolate the three-use qubit obstruction to arbitrary $N,d$.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 10, §VI: the first two training calls may be parallel for general N

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF pp.10-11, (84)-(88), conclusion: for every N>=2 there is a global
optimizer whose first two training uses are parallel. Later calls remain causal. -/
theorem first_two_parallel (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    ∃ R : Branches d N, IsOptimal (by omega : 0 < d) R ∧
      IsLearningSymmetric R ∧ LearningInstrument 2 R := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
