-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_relabel_replacement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.relabel_replacement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:29:45.046868+00:00
-- url     : https://prove2.me/theorems/35393f95-169a-422c-991b-fd6862d4354e
-- title:
--   Simultaneous outcome relabeling and the seed symmetry
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Assume $N\ge1$, and let $S$ be an admissible diagonal covariant learner. Average over a single permutation $\sigma\in S_d$ applied to the replica label and every original classical label, leaving the quantum input coordinates fixed. The resulting learner $R$ is admissible, diagonal, covariant, relabel-invariant, and $D(R)\le D(S)$. In branch notation it obeys the paper's classical conjugation identity (28). For its seed,
--
--   $$G_{\sigma(i)}^R(I)=T_\sigma G_i^R(I)T_\sigma^\dagger.$$
--
--   Here $T_\sigma|i\rangle=|\sigma(i)\rangle$. Odd permutations are accommodated inside $SU(d)$ by multiplying $T_\sigma$ by a scalar phase correcting its determinant; the conjugation action is unchanged. The $M$ after (28) means $N$. This justifies the label reduction.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 5, Lemma 4 (Relabeling symmetry)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF p.5, Lemma 4, (28)-(32): classical relabeling average and seed identity.
The undefined M after (28) means N. Odd permutation matrices are implemented
in covariance by a determinant-correcting scalar phase, not by enlarging SU(d). -/
theorem relabel_replacement {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    (S : Branches d N) (hS : LearningInstrument 0 S)
    (hdiag : IsDiagonal S) (hcov : IsLearningCovariant S) :
    LearningInstrument 0 (relabelAverage S) ∧ IsLearningSymmetric (relabelAverage S) ∧
    learningDistance (by omega : 0 < d) (relabelAverage S) ≤
      learningDistance (by omega : 0 < d) S ∧
    ∀ sigma : Equiv.Perm (Fin d), ∀ i a b,
      replicatedPOVM (relabelAverage S) 1 (sigma i) (sigma a) (sigma b) =
        replicatedPOVM (relabelAverage S) 1 i a b := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
