-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_twoQudit_reconstruction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.twoQudit_reconstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:02:45.51073+00:00
-- url     : https://prove2.me/theorems/dfc705b9-894e-4287-ae6a-3525d10861bf
-- title:
--   Two-qudit reconstruction coefficients and endpoint maps
-- statement:
--   Let $N=2$, $d\ge2$, and let a locally scrambled projective experiment have second features $(1,w,w,1)$ in region order $\varnothing,\{1\},\{2\},\{1,2\}$, with $2d/(d^2+1)\le w\le1$. Its unique coefficient solution is
--
--   $$\begin{aligned}r_\varnothing&=\frac{d^3w-3d^2+3dw-2w^2+1}{(dw-1)(d^2-2dw+1)},\\r_{\{1\}}=r_{\{2\}}&=\frac{-d^4w+2d^3-2d+w}{d(dw-1)(d^2-2dw+1)},\\r_{\{1,2\}}&=\frac{(d^2-1)^2}{d^2(d^2-2dw+1)}.\end{aligned}$$
--
--   The constructed map $\mathcal R_w(X)=d^2\sum_A r_A X_A$ is a two-sided inverse of the measurement channel. At the endpoints,
--
--   $$\mathcal R_1=\mathcal L_d\otimes\mathcal L_d,\qquad \mathcal L_d(X)=(d+1)X-\operatorname{Tr}(X)I,\qquad \mathcal R_{2d/(d^2+1)}(X)=(d^2+1)X-\operatorname{Tr}(X)I.$$
--
--   For product inputs the local endpoint is $\mathcal L_d(X)\otimes\mathcal L_d(Y)$. The tensor-of-maps formulation covers correlated inputs without factoring their marginals.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 5, §II C, Eqs.(24)–(28): two-qudit reconstruction coefficients

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

/-- PDF pp.5–6 Eqs.(24)–(28): exact toy-model coefficients and the local/global
endpoint superoperators. Eq.(27) is a tensor of maps on general inputs, with a
product-input specialization; Eq.(28) contains Tr(X) I on arbitrary X. -/
theorem twoQudit_reconstruction {d : ℕ} (hd : 2 ≤ d) (E : ProjectiveEnsemble 2 d)
    (hls : LocallyScrambled (prior E)) (w : ℝ)
    (hw : 2*(d : ℝ)/((d : ℝ)^2+1) ≤ w ∧ w ≤ 1) (hf : ToyFeature (prior E) w) :
    CoefficientSystem (prior E) (toyCoefficients d w) ∧
    (∀ r, CoefficientSystem (prior E) r → r = toyCoefficients d w) ∧
    (∀ X : Op 2 d,
      efReconstruct (toyCoefficients d w) (snapshotMeasurementMap (prior E) X) = X ∧
      snapshotMeasurementMap (prior E) (efReconstruct (toyCoefficients d w) X) = X) ∧
    (∀ X : Op 2 d, efReconstruct (toyCoefficients d 1) X =
      QAlgorithms.piSuperop (fun _ : Fin 2 => oneSiteInverse d) X) ∧
    (∀ X Y : Matrix (Fin d) (Fin d) ℂ,
      efReconstruct (toyCoefficients d 1) (twoSiteProduct X Y) =
        twoSiteProduct (oneSiteInverse d X) (oneSiteInverse d Y)) ∧
    (∀ X : Op 2 d,
      efReconstruct (toyCoefficients d (2*(d : ℝ)/((d : ℝ)^2+1))) X =
        ((d : ℂ)^2+1) • X - X.trace • 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
