-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_three_use_requires_adaptation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.three_use_requires_adaptation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:26:55.288743+00:00
-- url     : https://prove2.me/theorems/3d9d1860-005e-4a78-9cdb-01cf2b8402cf
-- title:
--   Three-example qubit learning requires adaptation
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   In this learning model take $d=2$ and $N=3$. There exists an optimal symmetric learner whose first two source calls are parallel and whose third call is later. Every globally optimal learner, including nonsymmetric learners, obeys
--
--   $$R\text{ optimal}\quad\Longrightarrow\quad R\text{ is not an all-three-parallel learner}.$$
--
--   This pins the exact causal obstruction; it makes no numerical claim about the approximate score $0.87$ and no assertion about all possible classical-program storage models.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 1, Abstract; §V.C and Remark 1: optimal three-example qubit learning requires adaptation

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF pp.9-10, V.C and Remark 1: exact qualitative qubit three-example
obstruction, including nonsymmetric parallel learners. Approximate 0.87 is
not promoted to an exact value. The first two calls may be parallel, but the
last call requires adaptation to their classical outputs. The separate broad
claim about all classical-only program models is deferred in HARD.md. -/
theorem three_use_requires_adaptation :
    (∃ R : Branches 2 3, IsOptimal (by decide : 0 < 2) R ∧
      IsLearningSymmetric R ∧ LearningInstrument 2 R) ∧
    (∀ R : Branches 2 3, IsOptimal (by decide : 0 < 2) R → ¬ LearningInstrument 3 R) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
