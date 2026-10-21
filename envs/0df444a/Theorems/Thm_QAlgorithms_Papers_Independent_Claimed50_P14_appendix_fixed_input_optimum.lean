-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P14_appendix_fixed_input_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P14.appendix_fixed_input_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:36:09.591311+00:00
-- url     : https://prove2.me/theorems/61b4aea3-d706-4797-b868-14ee87a2bdfd
-- title:
--   Fixed-input sector optima and simultaneous physical attainment
-- statement:
--   Let $d\ge2$ and let $E_i(U)=U|i\rangle\langle i|U^\dagger$, $i=1,\ldots,d$, be the unknown labeled nondegenerate projective measurement on $\mathbb C^d$, with $U\in SU(d)$. Its device returns only the classical outcome, as the channel $\rho\mapsto\sum_i\operatorname{Tr}(E_i(U)\rho)|i\rangle\langle i|$. The same unknown device is called $N$ times, all before the target state arrives, and one $d$-outcome replica $G^R(U)$ is produced. A learner $R$ consists of positive unnormalized Choi branches whose sum satisfies all recursive causal trace constraints; arbitrary finite quantum memory is allowed, and its operations are independent of $U$. Write $D(R)$ for the normalized Haar average over $SU(d)$ and unit pure target states of the sum of squared differences of outcome probabilities. Write $F(R)=d^{-1}\int\sum_i\operatorname{Tr}(E_i(U)G_i^R(U))\,dU$ for the Haar-averaged overlap, which equals the paper's seed overlap on covariant learners. An optimum minimizes $D$ over the full causal domain.
--
--   Take $N=2$ and fix $t_\pm\ge0$ with $d_+t_++d_-t_-=1$, where $d_\pm=d(d\pm1)/2$. Use the actual alpha embedding $|\Psi_m^\pm\rangle$, beta and gamma projectors of (40),(42). For classes $xxx,xxy,xyx,xyy,xyz$, let $s^\nu$ be the rescaled blocks (A2), satisfying positivity, swap symmetry and all equalities (A4),(A5). At $d=2$ the gamma and xyz sectors are absent. Reconstruction yields an admissible symmetric parallel learner with input density $T=t_+P_++t_-P_-$ and every slice sum $I\otimes T$. Its score is $F=F_\alpha+F_\beta+F_\gamma$, and
--
--   $$F_\alpha\le\frac{d+3}{2(d+1)}t_++\sqrt{\frac{d-1}{d+1}}\sqrt{t_+t_-}+\frac12t_-,\quad F_\beta\le\begin{cases}4t_+/3&d=2,\\(d+1)t_+/2&d\ge3,\end{cases}\quad F_\gamma\le\begin{cases}0&d=2,\\(d-1)t_-/2&d\ge3.\end{cases}$$
--
--   All three bounds are attained simultaneously. In order $xxx,xxy,xyx,xyy,xyz$, put $Z=\operatorname{diag}(1,-1)$, $A=\frac{d-1}{2}\begin{pmatrix}t_+&\sqrt{t_+t_-}\\\sqrt{t_+t_-}&t_-\end{pmatrix}$ and take alpha blocks $(\operatorname{diag}(t_+,t_-),A,ZAZ,0,0)$. For $d\ge3$ take beta blocks $(0,0,0,t_+,(d-1)t_+)$ and gamma blocks $(0,0,0,t_-,(d-1)t_-)$. For $d=2$ take beta blocks $(0,t_+/2,t_+/2,t_+,0)$ and zero gamma blocks. These attain the corrected scalar objective of the global two-use theorem. No division by the absent qubit xyz multiplicity occurs. This preserves the sector optimization and its concrete physical witness.
-- source:
--   Quantum learning algorithms for quantum measurements, arXiv:1103.0480v2, PDF p. 11, Appendix A: fixed-input two-use optimization and attaining blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF pp.11-12, Appendix A, (A1)-(A13), CORRECTED as documented above:
sector upper bounds, simultaneous attainment by physical representation blocks,
and the fixed-input optimal score. No absent xyz division is used at d=2. -/
theorem appendix_fixed_input_optimum (d : ℕ) (hd : 2 ≤ d)
    (tp tm : ℝ) (ht : FixedInputParameters d tp tm) :
    (∀ B : TwoUseBlocks, FeasibleBlocks d tp tm B →
      LearningInstrument 2 (blockInstrument d B) ∧ IsLearningSymmetric (blockInstrument d B) ∧
      (∀ j, ∑ i, outcomeBlocks (blockInstrument d B) i j =
        Matrix.kronecker (1 : (Matrix (Fin d) (Fin d) ℂ))
          ((tp : ℂ) • sourceSymmetric d + (tm : ℂ) • sourceAntisymmetric d)) ∧
      sectorAlpha d B ≤ (d+3 : ℝ)/(2*(d+1))*tp +
        Real.sqrt ((d-1 : ℝ)/(d+1))*Real.sqrt (tp*tm) + tm/2 ∧
      sectorBeta d B ≤ (if d = 2 then (4/3 : ℝ)*tp else (d+1 : ℝ)*tp/2) ∧
      sectorGamma d B ≤ (if d = 2 then 0 else (d-1 : ℝ)*tm/2) ∧
      learningScore (blockInstrument d B) = sectorAlpha d B + sectorBeta d B + sectorGamma d B ∧
      learningScore (blockInstrument d B) ≤ twoUseScalarObjective d tp tm) ∧
    (let B := twoUseAttainingBlocks d tp tm
     FeasibleBlocks d tp tm B ∧
     LearningInstrument 2 (blockInstrument d B) ∧ IsLearningSymmetric (blockInstrument d B) ∧
     sectorAlpha d B = (d+3 : ℝ)/(2*(d+1))*tp +
       Real.sqrt ((d-1 : ℝ)/(d+1))*Real.sqrt (tp*tm) + tm/2 ∧
     sectorBeta d B = (if d = 2 then (4/3 : ℝ)*tp else (d+1 : ℝ)*tp/2) ∧
     sectorGamma d B = (if d = 2 then 0 else (d-1 : ℝ)*tm/2) ∧
     learningScore (blockInstrument d B) = twoUseScalarObjective d tp tm) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P14

end
