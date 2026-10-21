-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P24_estimateAndReprepare
-- name    : QAlgorithms.Papers.Independent.Next46.P24.estimateAndReprepare
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:56:47.137816+00:00
-- url     : https://prove2.me/theorems/92814540-8102-4e9e-b627-ec3b8552e59a
-- title:
--   Unnumbered physical inversion realization, Eqs.(12)–(14) and Fig.4: estimate and re-prepare
-- statement:
--   Let $d\ge2$, let $C=C_{\mathrm{opt}}=P^+_{31}\otimes P^+_{20}/d_++P^-_{31}\otimes P^-_{20}/d_-$, and use fixed coordinate bases and normalized Haar measure on $SU(d)$. Here $d_\pm=d(d\pm1)/2$, $P^\pm=(I\pm\mathrm{Swap})/2$, and every paired operator is permuted into wire order $3210$. Put $P=P^+_{31}\otimes P^+_{20}+P^-_{31}\otimes P^-_{20}$, the support projector of $C^*$. This is the orthogonal projector with the same kernel as $C$. The two fixed stages are
--
--   $$
--   V_1=d^{-1/2}|I\rangle\!\rangle_{11'}\otimes T_{0\to0'},\qquad
--   V_2=\sqrt d\,(I_3\otimes\sqrt{C^*})\bigl(|I\rangle\!\rangle_{33'}\otimes T_{2\to2'}\bigr),
--   $$
--
--   with identity extensions on the stored registers. They are isometries, their sequential contraction has Choi operator $C$, and the second stage takes values in $H_3\otimes\operatorname{Supp}(C^*)$. Its ambient-coordinate square root and inverse square root are $S=\sum_{\mu=\pm}d_\mu^{-1/2}P^\mu_{31}\otimes P^\mu_{20}$ and $R=\sum_{\mu=\pm}d_\mu^{1/2}P^\mu_{31}\otimes P^\mu_{20}$: $S^2=C^*$ and $SR=P$, with both operators zero on the complementary sectors.
--
--   For an estimate $\widehat U\in SU(d)$ define
--
--   $$
--   Q_{\widehat U}=R\Bigl(|\widehat U^T\rangle\!\rangle\langle\!\langle\widehat U^T|_{3'0'}\otimes|\widehat U\rangle\!\rangle\langle\!\langle\widehat U|_{2'1'}\Bigr)R.
--   $$
--
--   These operators are positive, supported on $P$, integrable, and satisfy $\int Q_{\widehat U}\,d\widehat U=P$. Thus their restriction is a POVM on $A_2=\operatorname{Supp}(C^*)$. The training POVM densities $M_{\widehat U}=d|\widehat U\rangle\!\rangle\langle\!\langle\widehat U|_{2'1'}$ are positive, integrable, and integrate to the identity on the training pair. For every density operator $\rho$ on $H_2\otimes H_{1'}\otimes H_{0'}$, the second channel is a density operator and obeys the actual channel identity
--
--   $$
--   \mathcal E(\rho)=\operatorname{Tr}_{A_2}(V_2\rho V_2^\dagger)
--   =\int\operatorname{Tr}_{A_2}\!\bigl[V_2\rho V_2^\dagger(I_3\otimes Q_{\widehat U})\bigr]\,d\widehat U
--   =d\int\widehat U^\dagger\langle\!\langle\widehat U|_{2'1'}\rho|\widehat U\rangle\!\rangle_{2'1'}\widehat U\,d\widehat U.
--   $$
--
--   Both channel integrands are integrable. For every unknown $U\in SU(d)$ and every input density operator $\sigma$ on wire $0$, applying $U$ to the first stage's training output gives the density operator $d^{-1}|U\rangle\!\rangle\langle\!\langle U|_{21'}\otimes\sigma_{0'}$. Hence the optimal comb is physically realized by measuring the training registers and conditionally applying the inverse estimate to the stored input. This identifies the full channel, including its action on correlations with the stored register.
--
--   **Formalization Note** The un-hatted estimated-unitary factors in Eq. (14) and its following POVM formula are read as $\widehat U$, and the post-call training wire is $2$ rather than the printed $1$. Completeness is asserted on the support, not on the ambient kernel.
-- source:
--   Minimal computational-space implementation of multi-round quantum protocols, arXiv:1006.1780v1, PDF p. 3, Unnumbered physical inversion realization, Eqs.(12)–(14) and Fig.4: estimate and re-prepare

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P24

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P24

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.combContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.pairContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.wireContinuousENorm

/-- PDF pp.3-4, Eqs.(12)-(14) and Fig.4: the actual estimate-and-reprepare realization.
Ambient memory is restricted by the explicit support projector. Both POVM completeness
and equality of the channels (not just their scores) are asserted. Missing hats and the
post-call wire label are corrected as required by the integral and the physical wiring.
All integrability claims follow from the construction, rather than being hypotheses. -/
theorem estimateAndReprepare (d : ℕ) (hd : 2 ≤ d) :
    (inversionFirstStage d)ᴴ * inversionFirstStage d = 1 ∧
    (secondIsometry d)ᴴ * secondIsometry d = 1 ∧
    optimalSupport d * optimalSupport d = optimalSupport d ∧
    (optimalSupport d)ᴴ = optimalSupport d ∧
    (∀ v : InversionWires d → ℂ,
      (optimalComb d).mulVec v = 0 ↔ (optimalSupport d).mulVec v = 0) ∧
    optimalRoot d * optimalRoot d = optimalComb d ∧
    optimalRoot d * optimalInverseRoot d = optimalSupport d ∧
    Matrix.kronecker (1 : Matrix (Fin d) _ ℂ) (optimalSupport d) *
      secondIsometry d = secondIsometry d ∧
    networkChoi d = optimalComb d ∧
    Integrable (@memoryPOVM d) (haar d) ∧
    (∫ Uhat, memoryPOVM Uhat ∂haar d) = optimalSupport d ∧
    (∀ Uhat : (Matrix.specialUnitaryGroup (Fin d) ℂ), (memoryPOVM Uhat).PosSemidef ∧
      optimalSupport d * memoryPOVM Uhat * optimalSupport d = memoryPOVM Uhat) ∧
    Integrable (@trainingPOVM d) (haar d) ∧
    (∫ Uhat, trainingPOVM Uhat ∂haar d) = 1 ∧
    (∀ Uhat : (Matrix.specialUnitaryGroup (Fin d) ℂ), (trainingPOVM Uhat).PosSemidef) ∧
    (∀ rho : Matrix (Training d) (Training d) ℂ, IsDensityMatrix rho →
      IsDensityMatrix (secondChannel rho) ∧
      Integrable (memoryBranch rho) (haar d) ∧
      Integrable (feedForwardBranch rho) (haar d) ∧
      secondChannel rho = ∫ Uhat, memoryBranch rho Uhat ∂haar d ∧
      secondChannel rho = ∫ Uhat, feedForwardBranch rho Uhat ∂haar d) ∧
    (∀ (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) (sigma : Matrix (Fin d) (Fin d) ℂ), IsDensityMatrix sigma →
      trainingPreparation U * sigma * (trainingPreparation U)ᴴ = preparedState U sigma ∧
      IsDensityMatrix (preparedState U sigma)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P24

end
