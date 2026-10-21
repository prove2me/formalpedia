-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_two_use_parallel
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.two_use_parallel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:33:42.50598+00:00
-- url     : https://prove2.me/theorems/b47bee6f-94ba-4eaf-b27f-ca59c05a6cba
-- title:
--   A two-example global optimum can be parallel
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Take $N=2$. Every admissible symmetric learner has a positive trace-one two-source input operator $T$ satisfying
--
--   $$\sum_i R'_{i,jk}=I_{\rm target}\otimes T\quad\text{for every }j,k,\qquad [T,U\otimes U]=0.$$
--
--   It therefore obeys the parallel causal normalization. In particular, a globally optimal symmetric learner exists with both source calls parallel. The operator $T$ and all slice equalities are conclusions, not hypotheses on an optimizer. This establishes unrestricted attainability by parallel training.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 8, §V.B, Eqs.(73)–(77): two-use learning can be parallelized

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF pp.8-9, (73)-(77): symmetrized two-use optimizers are parallel;
retain the PSD trace-one input T and every classical-slice normalization. -/
theorem two_use_parallel (d : ℕ) (hd : 2 ≤ d) :
    (∀ R : Branches d 2, LearningInstrument 0 R → IsLearningSymmetric R →
      ∃ T : Matrix (Labels d 2) (Labels d 2) ℂ,
        T.PosSemidef ∧ T.trace = 1 ∧ LearningInstrument 2 R ∧
        (∀ j, ∑ i, outcomeBlocks R i j = Matrix.kronecker (1 : (Matrix (Fin d) (Fin d) ℂ)) T) ∧
        (∀ U : SU d, T * inputTensorPower (U : (Matrix (Fin d) (Fin d) ℂ)) = inputTensorPower (U : (Matrix (Fin d) (Fin d) ℂ)) * T)) ∧
    ∃ R : Branches d 2, IsOptimal (by omega : 0 < d) R ∧
      IsLearningSymmetric R ∧ LearningInstrument 2 R := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
