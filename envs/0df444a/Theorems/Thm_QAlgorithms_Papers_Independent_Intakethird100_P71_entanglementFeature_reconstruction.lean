-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_entanglementFeature_reconstruction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.entanglementFeature_reconstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:58:04.632944+00:00
-- url     : https://prove2.me/theorems/9c8152b0-de32-4df6-9f46-f278ba667493
-- title:
--   Entanglement features determine unbiased reconstruction
-- statement:
--   Let a fixed Borel probability ensemble of unitaries measure $N$ qudits of dimension $d\ge2$, with $D=d^N$. A raw snapshot is $S=U^\dagger|b\rangle\langle b|U$. The prior chooses $b$ uniformly; the posterior weights the prior by $D\operatorname{Tr}(S\rho)$. Assume the prior law is invariant under every local conjugation and its measurement channel $\mathcal M(X)=D\mathbb E[S\operatorname{Tr}(SX)]$ is injective. For every region $A$, let $X_A$ denote the partial trace over its complement, tensored with normalized identity in the original site order, and let $W_C=\mathbb E\operatorname{Tr}[(\operatorname{Tr}_{\bar C}S)^2]$. Then
--
--   $$\mathcal M(X)=\sum_{B,C}d^{2N-|B|}X_B\,\mathrm{Wg}_{B,C}W_C,\qquad \mathrm{Wg}_{B,C}=(d^2-1)^{-N}(-1/d)^{|B\triangle C|}.$$
--
--   There is a unique real coefficient vector $r$ solving $\sum_{A,C}r_A f_{A,B,C}W_C=\delta_{B,\Omega}$, where $f$ is the explicit fusion coefficient of Eq. (11). For every operator $X$ and every density matrix $\rho$,
--
--   $$\mathcal R(X)=d^N\sum_A r_A X_A=\mathcal M^{-1}(X),\qquad \mathbb E_{S\mid\rho}\mathcal R(S)=\rho.$$
--
--   Consequently every Hermitian observable has an unbiased linear prediction. The same coefficients work for all input states; their computation is not claimed efficient.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 1, Abstract / §II A: entanglement-feature reconstruction and unbiased classical shadows

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P71

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Intakethird100.P71

attribute [local instance] Classical.propDecidable

local notation "Config" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Config (P := Fin n) (fun _ => d)

local notation "Op" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Op (Config n d)

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P71.matrixContinuousENorm

local notation "Unitary" n:max d:max => Matrix.unitaryGroup (Config n d) ℂ

local notation "Local" n:max d:max => Fin n → Matrix.unitaryGroup (Fin d) ℂ

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.3–4 Eqs.(7),(9),(11),(12), Appendix A p.18: EF channel formula,
unique reconstruction coefficients under completeness, and unbiased shadows.
The coefficients are chosen once from the ensemble, before rho. -/
theorem entanglementFeature_reconstruction {n d : ℕ} (hd : 2 ≤ d) (E : ProjectiveEnsemble n d)
    (hls : LocallyScrambled (prior E)) (hc : Complete (prior E)) :
    (∀ X : Op n d, snapshotMeasurementMap (prior E) X =
      ∑ B : Finset (Fin n), ∑ C : Finset (Fin n),
        ((((d : ℝ)^(2*n) / (d : ℝ)^B.card) * regionalWg n d B C *
          feature (prior E) C : ℝ) : ℂ) • reducedSnapshot B X) ∧
    ∃! r : Finset (Fin n) → ℝ,
      CoefficientSystem (prior E) r ∧
      (∀ X : Op n d, efReconstruct r X = snapshotInverse (prior E) hc X) ∧
      (∀ rho : Op n d, IsDensityMatrix rho →
        Integrable (fun S => efReconstruct r S) (posteriorOf (prior E) rho) ∧
        (∫ S, efReconstruct r S ∂posteriorOf (prior E) rho) = rho ∧
        ∀ O : Op n d, O.IsHermitian →
          (∫ S, shadowEstimate (prior E) hc O S ∂posteriorOf (prior E) rho) = (O*rho).trace.re) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
