-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_localGlobal_randomObservableComparison
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.localGlobal_randomObservableComparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:04:08.732796+00:00
-- url     : https://prove2.me/theorems/298b1b56-92a4-4d50-ab3e-634f9af4ea97
-- title:
--   Local and global random-observable comparison, with source correction
-- statement:
--   Consider the complete locally scrambled two-qudit toy experiment with $d\ge2$, $2d/(d^2+1)\le w\le1$, snapshot features $(1,w,w,1)$, and local-state averaged second moment $Q_{\mathrm{av}}$. Every traceless Hermitian local observable $O_{\rm loc}=A\otimes I$ satisfies
--
--   $$Q_{\mathrm{av}}(O_{\rm loc})=\frac{d^2-1}{d^2(dw-1)}\operatorname{Tr}(O_{\rm loc}^2).$$
--
--   For a trace-removed global GUE observable $G$, in ensemble expectation,
--
--   $$\mathbb E_G Q_{\mathrm{av}}(G)=\frac{d^2-1}{d^2(d^2+1)}\left(\frac{(d^2-1)^2}{d^2-2dw+1}+\frac{2}{dw-1}\right)\mathbb E_G\operatorname{Tr}(G^2).$$
--
--   The Gaussian integrands are integrable. At $w=2d/(d^2+1)$ every traceless Hermitian $O$ has $Q_{\mathrm{av}}(O)=(1+d^{-2})\operatorname{Tr}(O^2)$. This compares second moments at a fixed Hilbert–Schmidt scale.
--
--   **Source correction.** The printed global denominator in Eq. (34) is $d^2-2dw-1$; it is changed to $d^2-2dw+1$, as forced by Eq. (31). The printed expression is negative at $d=2,w=4/5$. The global formula is an ensemble assertion, not an identity for each GUE draw. Independent moderation of this correction is pending.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 6, §II C, Eqs.(32)–(34): local/global random-observable comparison, with correction

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

/-- PDF p.6 Eqs.(32)–(34), corrected consequence of Eq.(31).
Printed: d²−2dw−1 in the global denominator. Changed: d²−2dw+1.
Why: Eq.(31) forces +1; at d=2,w=4/5 the printed expression is negative.
The global GUE statement is an ensemble expectation, not an identity for each
random draw. Traces are removed to obey the section's traceless convention.
This source correction requires independent moderation. -/
theorem localGlobal_randomObservableComparison {d : ℕ} (hd : 2 ≤ d) (E : ProjectiveEnsemble 2 d)
    (hls : LocallyScrambled (prior E)) (hc : Complete (prior E))
    (w : ℝ) (hw : 2*(d : ℝ)/((d : ℝ)^2+1) ≤ w ∧ w ≤ 1) (hf : ToyFeature (prior E) w)
    (H : Measure (Local 2 d)) [IsProbabilityMeasure H] [H.IsMulLeftInvariant]
    (rho : Op 2 d) (hrho : IsDensityMatrix rho) :
    (∀ A : Matrix (Fin d) (Fin d) ℂ, A.IsHermitian → A.trace = 0 →
      averagedSecondMoment H (prior E) hc rho (localObservable A) =
        ((d : ℝ)^2-1)/((d : ℝ)^2*((d : ℝ)*w-1)) * hsSquare (localObservable A)) ∧
    Integrable (fun z => averagedSecondMoment H (prior E) hc rho (gueOperator d z)) (gueCoordinates d) ∧
    Integrable (fun z => hsSquare (gueOperator d z)) (gueCoordinates d) ∧
    (∫ z, averagedSecondMoment H (prior E) hc rho (gueOperator d z) ∂gueCoordinates d) =
      ((d : ℝ)^2-1)/((d : ℝ)^2*((d : ℝ)^2+1)) *
        (((d : ℝ)^2-1)^2/((d : ℝ)^2-2*(d : ℝ)*w+1) + 2/((d : ℝ)*w-1)) *
          (∫ z, hsSquare (gueOperator d z) ∂gueCoordinates d) ∧
    (∀ X : Op 2 d, X.IsHermitian → X.trace = 0 →
      (w = 2*(d : ℝ)/((d : ℝ)^2+1) →
        averagedSecondMoment H (prior E) hc rho X = (1 + ((d : ℝ)^2)⁻¹) * hsSquare X)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
