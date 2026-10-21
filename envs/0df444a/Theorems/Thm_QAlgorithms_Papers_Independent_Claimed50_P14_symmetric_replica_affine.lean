-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_symmetric_replica_affine
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.symmetric_replica_affine
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:31:22.138977+00:00
-- url     : https://prove2.me/theorems/0b43f173-d4ec-45b5-9226-7d692adf93ec
-- title:
--   Corrected affine form of a symmetric replica
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Assume $N\ge1$ and let $R$ be admissible, diagonal, covariant and invariant under simultaneous outcome relabeling. There is one real number $\lambda$, independent of $U$ and $i$, such that
--
--   $$-\frac1{d-1}\le\lambda\le1,\qquad G_i^R(U)=\lambda E_i(U)+\frac{1-\lambda}{d}I.$$
--
--   If $R$ is globally optimal for $D$, then $\lambda\ge0$, so the affine expression is then a random mixture of the perfect and trivial measurements. For arbitrary symmetric learners the printed nonnegative range is false; its separate inventory node remains deferred with a counterexample. This theorem retains the valid structure without assuming the missing conclusion.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 6, Lemma 5, corrected affine form of the replicated POVM

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF pp.6-7, Lemma 5, (43)-(49), CORRECTED: all symmetric learners
have -1/(d-1) <= lambda <= 1; only an optimal symmetric learner must
have lambda >= 0. The printed unrestricted mixture interpretation is false. -/
theorem symmetric_replica_affine {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    (R : Branches d N) (hR : LearningInstrument 0 R) (hs : IsLearningSymmetric R) :
    ∃ lam : ℝ, -(1/(d-1 : ℝ)) ≤ lam ∧ lam ≤ 1 ∧
      (∀ U : SU d, ∀ i, replicatedPOVM R (U : (Matrix (Fin d) (Fin d) ℂ)) i =
        (lam : ℂ) • measurementFamily (U : (Matrix (Fin d) (Fin d) ℂ)) i +
        (((1-lam)/(d : ℝ) : ℝ) : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ))) ∧
      (IsOptimal (by omega : 0 < d) R → 0 ≤ lam) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
