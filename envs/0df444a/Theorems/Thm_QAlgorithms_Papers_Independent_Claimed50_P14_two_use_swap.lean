-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_two_use_swap
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.two_use_swap
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:34:34.278258+00:00
-- url     : https://prove2.me/theorems/4eec8172-ff6a-452e-9e40-5a3f8ae2c820
-- title:
--   Swap averaging of parallel two-example learners
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Take $N=2$ and an admissible symmetric parallel learner $R$. Let $S$ swap only the two original quantum input wires, and average
--
--   $$\widetilde R'_{i,jk}=\tfrac12\bigl(R'_{i,jk}+S R'_{i,kj}S\bigr).$$
--
--   The new learner is admissible, symmetric and parallel, with $\widetilde R'_{i,jk}=S\widetilde R'_{i,kj}S$. It has the same $F$, and the sum over replica labels of each classical slice is unchanged. If $R$ is globally optimal, so is $\widetilde R$. The target register is fixed. This supplies the actual swap transport rather than a condition on arbitrary multiplicity blocks.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 9, Lemma 6: swap symmetry for parallel two-use learning

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF p.9, Lemma 6: actual source-input and original-outcome swap transport.
Target wire 4 is fixed. Normalization and the seed score are preserved. -/
theorem two_use_swap {d : ℕ} (hd : 2 ≤ d) (R : Branches d 2)
    (hR : LearningInstrument 2 R) (hs : IsLearningSymmetric R) :
    LearningInstrument 2 (swapAverage R) ∧ IsLearningSymmetric (swapAverage R) ∧
    swapAverage R = swapLearner (swapAverage R) ∧
    learningScore (swapAverage R) = learningScore R ∧
    (∀ j, ∑ i, outcomeBlocks (swapAverage R) i j = ∑ i, outcomeBlocks R i j) ∧
    (IsOptimal (by omega : 0 < d) R → IsOptimal (by omega : 0 < d) (swapAverage R)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
