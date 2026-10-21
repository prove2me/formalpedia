-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_two_use_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.two_use_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:35:24.543885+00:00
-- url     : https://prove2.me/theorems/8cafa0ae-73b5-42bf-9b2d-e0201f633c6b
-- title:
--   Corrected global two-example optimum with attaining blocks
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Take $N=2$, and write $d_\pm=d(d\pm1)/2$. Among $t_\pm\ge0$ with $d_+t_++d_-t_-=1$, the scalar objective attains a maximum, where
--
--   $$f_d(t_+,t_-)=\begin{cases}\frac{13}{6}t_++\frac12t_-+\sqrt{t_+t_-/3},&d=2,\\\frac{d^2+3d+4}{2(d+1)}t_++\sqrt{\frac{d-1}{d+1}}\sqrt{t_+t_-}+\frac d2t_-,&d\ge3.\end{cases}$$
--
--   At a maximizing pair, the concrete physical learner reconstructed from the Appendix A attaining blocks is symmetric, parallel and globally $D$-optimal; its $F$ is $f_d(t_+,t_-)$ and bounds the $F$ of every unrestricted admissible learner. Its every-$U$ replica is
--
--   $$G_i^R(U)=\frac{dF(R)-1}{d-1}E_i(U)+\frac{1-F(R)}{d-1}I.$$
--
--   The reconstruction uses the actual vectors $|\Psi_m^\pm\rangle=(|\omega\rangle|m\rangle\pm|m\rangle|\omega\rangle)/\sqrt{2(d\pm1)}$, their alpha embedding, and the complementary beta and gamma projectors on physical target and source wires. Thus this is attained operational optimization, not an unguarded real supremum. The printed (82),(A14) are corrected from their sector derivation and retained separately as a false printed claim.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 8, §V.B: global two-use optimum, corrected from Appendix A

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF pp.8-9,12, global two-use optimization, CORRECTED from Appendix A.
Attainment includes actual alpha embeddings and beta/gamma assignments, not
an abstract decomposition assumed as a witness. -/
theorem two_use_optimum (d : ℕ) (hd : 2 ≤ d) :
    ∃ tp tm : ℝ, FixedInputParameters d tp tm ∧
      (∀ u v : ℝ, FixedInputParameters d u v →
        twoUseScalarObjective d u v ≤ twoUseScalarObjective d tp tm) ∧
      (let R := blockInstrument d (twoUseAttainingBlocks d tp tm)
       LearningInstrument 2 R ∧ IsLearningSymmetric R ∧ IsOptimal (by omega : 0 < d) R ∧
       learningScore R = twoUseScalarObjective d tp tm ∧
       (∀ S : Branches d 2, LearningInstrument 0 S →
          learningScore S ≤ learningScore R) ∧
       ∀ U : SU d, ∀ i, replicatedPOVM R (U : (Matrix (Fin d) (Fin d) ℂ)) i =
         ((((d : ℝ)*learningScore R-1)/(d-1) : ℝ) : ℂ) • measurementFamily (U : (Matrix (Fin d) (Fin d) ℂ)) i +
         (((1-learningScore R)/(d-1) : ℝ) : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
