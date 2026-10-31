-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_quantumNeymanPearson
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.quantumNeymanPearson
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:57:31.203167+00:00
-- url     : https://prove2.me/theorems/8d670e35-4245-46d3-98b3-055dee776678
-- title:
--   Lemma 1, Quantum Neyman–Pearson
-- statement:
--   Let $\rho,\sigma$ be density operators, $T>0$, and $P_*$ the projector onto the range of $(T\sigma-\rho)_+$. For any effect $0\le P\le I$, define $\alpha(P)=\operatorname{Tr}(P\rho)$ and $\beta(P)=\operatorname{Tr}((I-P)\sigma)$. Then
--
--   $$\alpha(P)+T\beta(P)\ge\alpha(P_*)+T\beta(P_*)=T-\operatorname{Tr}(T\sigma-\rho)_+.$$
--
--   Moreover, $\alpha(P)\le\alpha(P_*)$ implies $\beta(P)\ge\beta(P_*)$. The strict positive spectral projector excludes the kernel, without any support-inclusion assumption.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 7, Lemma 1, Quantum Neyman–Pearson

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF p.7: Lemma 1, Quantum Neyman–Pearson. -/
theorem quantumNeymanPearson (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (T : ℝ) (hT : 0 < T) (P : Mat I) (hP : IsEffect P) :
    let Pstar := positiveProjection ((T : ℂ) • sigma-rho)
    IsProjection Pstar ∧ IsEffect Pstar ∧
    typeIError rho Pstar + T*typeIIError sigma Pstar ≤ typeIError rho P + T*typeIIError sigma P ∧
    typeIError rho Pstar + T*typeIIError sigma Pstar =
      T-(positivePart ((T : ℂ) • sigma-rho)).trace.re ∧
    (typeIError rho P ≤ typeIError rho Pstar → typeIIError sigma Pstar ≤ typeIIError sigma P) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
