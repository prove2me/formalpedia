-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_one_use_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.one_use_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:32:48.099755+00:00
-- url     : https://prove2.me/theorems/8fa4bdc5-adc7-4527-b1fe-a08e14ec983a
-- title:
--   Optimal one-example learner and its retrieval
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Take $N=1$. Let $|\omega\rangle=\sum_{a=1}^d|a,a\rangle$, $P_p=|\omega\rangle\langle\omega|/d$ and $P_q=I-P_p$. The classical slices of the concrete learner are
--
--   $$R'_{i,j}=\begin{cases}P_p/d&i=j,\\P_q/[d(d-1)]&i\ne j.\end{cases}$$
--
--   This is an admissible symmetric global optimum. Every admissible learner $S$ satisfies
--
--   $$F(S)\le F(R)=\frac{d+1}{d^2},\qquad D(R)=\frac d{d^2-1}\left(1-\frac{d+1}{d^2}\right)^2.$$
--
--   For every unknown $U$,
--
--   $$G_i^R(U)=\frac1{d(d-1)}E_i(U)+\frac{d^2-d-1}{d^2(d-1)}I.$$
--
--   Operationally prepare the normalized probe $|\omega\rangle\langle\omega|/d$ and query one half. Given its classical label $j$, retrieve on the later target and retained half using effect $P_p$ if $i=j$ and $P_q/(d-1)$ otherwise. These effects are a POVM; its probabilities for every target density matrix equal those of $G^R(U)$. Equivalently measure $\{P_p,P_q\}$, reporting $j$ on $p$ and a uniformly random different label on $q$. This states the implementation as well as its score.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 7, §V.A, Eqs.(59)–(64): optimal one-use learning and its implementation

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF pp.7-8, (59)-(64): unrestricted optimum, concrete attaining instrument,
every-U replica, normalized entangled probe and actual retrieval probabilities. -/
theorem one_use_optimum (d : ℕ) (hd : 2 ≤ d) :
    let R := oneUseOptimalInstrument d
    LearningInstrument 0 R ∧ IsLearningSymmetric R ∧ IsOptimal (by omega : 0 < d) R ∧
    learningScore R = (d+1 : ℝ)/(d : ℝ)^2 ∧
    (∀ S : Branches d 1, LearningInstrument 0 S →
      learningScore S ≤ (d+1 : ℝ)/(d : ℝ)^2) ∧
    learningDistance (by omega : 0 < d) R =
      (d : ℝ)/((d : ℝ)^2-1)*(1-(d+1 : ℝ)/(d : ℝ)^2)^2 ∧
    (∀ U : SU d, ∀ i, replicatedPOVM R (U : (Matrix (Fin d) (Fin d) ℂ)) i =
      (1/((d : ℝ)*(d-1)) : ℂ) • measurementFamily (U : (Matrix (Fin d) (Fin d) ℂ)) i +
      ((((d : ℝ)^2-d-1)/((d : ℝ)^2*(d-1)) : ℝ) : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ))) ∧
    IsDensityMatrix (oneUseProbe d) ∧
    (∀ j, IsPOVM (fun i => oneUseRetrieval d i j)) ∧
    (∀ U : SU d, ∀ rho : (Matrix (Fin d) (Fin d) ℂ), IsDensityMatrix rho → ∀ i,
      oneUseOperationalProbability (U : (Matrix (Fin d) (Fin d) ℂ)) rho i =
        effectProb (replicatedPOVM R (U : (Matrix (Fin d) (Fin d) ℂ)) i) rho) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
