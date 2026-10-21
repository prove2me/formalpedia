-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_score_distance_equivalence
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.score_distance_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:32:06.236985+00:00
-- url     : https://prove2.me/theorems/f7199e01-f0c9-4fe2-b64f-45499c5897f3
-- title:
--   Learning score, affine coefficient, and distance
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Assume $N\ge1$. For any admissible symmetric learner $R$,
--
--   $$D(R)=\frac d{d^2-1}(1-F(R))^2,\qquad \lambda=\frac{dF(R)-1}{d-1}.$$
--
--   Every seed diagonal entry $\langle i|G_i^R(I)|i\rangle$ equals $F(R)$, and
--
--   $$F(R)=\frac1d\sum_{i,j}\langle i,j|R'_{i,j}|i,j\rangle,\qquad G_i^R(U)=\frac{dF(R)-1}{d-1}E_i(U)+\frac{1-F(R)}{d-1}I.$$
--
--   Every unrestricted admissible learner has a symmetric admissible replacement with no greater $D$. A symmetric admissible learner is globally $D$-optimal if and only if its $F$ is maximal among all symmetric admissible learners. The optimization equivalence uses the constructive reductions rather than assuming symmetry for the original task.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 7, §IV, Eqs.(49)–(52): equivalent learning objectives

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF p.7, (49)-(52): exact symmetric-objective identities and unrestricted
optimality transport. Every denominator is real and d>=2. -/
theorem score_distance_equivalence {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N) :
    (∀ R : Branches d N, LearningInstrument 0 R → IsLearningSymmetric R →
      learningDistance (by omega : 0 < d) R =
        (d : ℝ)/((d : ℝ)^2-1)*(1-learningScore R)^2 ∧
      (∀ i, (replicatedPOVM R 1 i i i).re = learningScore R) ∧
      learningScore R = (∑ i, ∑ j : Labels d N,
        (outcomeBlocks R i j (i,j) (i,j)).re)/(d : ℝ) ∧
      (∀ U : SU d, ∀ i, replicatedPOVM R (U : (Matrix (Fin d) (Fin d) ℂ)) i =
        ((((d : ℝ)*learningScore R-1)/(d-1) : ℝ) : ℂ) • measurementFamily (U : (Matrix (Fin d) (Fin d) ℂ)) i +
        (((1-learningScore R)/(d-1) : ℝ) : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ)))) ∧
    (∀ S : Branches d N, LearningInstrument 0 S →
      ∃ R : Branches d N, LearningInstrument 0 R ∧ IsLearningSymmetric R ∧
        learningDistance (by omega : 0 < d) R ≤ learningDistance (by omega : 0 < d) S) ∧
    (∀ R : Branches d N, LearningInstrument 0 R → IsLearningSymmetric R →
      (IsOptimal (by omega : 0 < d) R ↔
        ∀ S : Branches d N, LearningInstrument 0 S → IsLearningSymmetric S →
          learningScore S ≤ learningScore R)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
