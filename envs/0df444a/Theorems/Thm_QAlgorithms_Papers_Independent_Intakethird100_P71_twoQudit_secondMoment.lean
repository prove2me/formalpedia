-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_twoQudit_secondMoment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.twoQudit_secondMoment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:03:27.823897+00:00
-- url     : https://prove2.me/theorems/8dd65eb1-b18f-43d9-9796-c7aa2e34c906
-- title:
--   Two-qudit second moment and operator locality
-- statement:
--   In the complete locally scrambled two-qudit toy experiment, let $d\ge2$, $2d/(d^2+1)\le w\le1$, and the snapshot features be $(1,w,w,1)$. Fix a density matrix $\rho$ and a traceless Hermitian observable $O$. Write $T=\operatorname{Tr}(O^2)$ and
--
--   $$K=\operatorname{Tr}[(\operatorname{Tr}_2O)^2]+\operatorname{Tr}[(\operatorname{Tr}_1O)^2].$$
--
--   The second moment averaged over local Haar conjugations of $\rho$ is
--
--   $$Q_{\mathrm{av}}(O)=\frac{d^2-1}{d^3}\left(\frac{K}{dw-1}+\frac{(d^2-1)(dT-K)}{d^2-2dw+1}\right).$$
--
--   For nonzero $O$, putting $k_{\rm tot}=K/T$ recovers Eq. (31). The undivided identity also includes $O=0$, where both sides vanish. This records the exact dependence on observable locality without introducing undefined purity ratios.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 6, §II C, Eqs.(29)–(31): two-qudit shadow norm

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

/-- PDF p.6 Eqs.(29)–(31): undivided two-qudit formula. K is the sum of the
unnormalized partial purities; for O≠0, k_tot=K/Tr(O²). O=0 is included. -/
theorem twoQudit_secondMoment {d : ℕ} (hd : 2 ≤ d) (E : ProjectiveEnsemble 2 d)
    (hls : LocallyScrambled (prior E)) (hc : Complete (prior E))
    (w : ℝ) (hw : 2*(d : ℝ)/((d : ℝ)^2+1) ≤ w ∧ w ≤ 1) (hf : ToyFeature (prior E) w)
    (H : Measure (Local 2 d)) [IsProbabilityMeasure H] [H.IsMulLeftInvariant]
    (rho O : Op 2 d) (hrho : IsDensityMatrix rho) (hO : O.IsHermitian) (ht : O.trace = 0) :
    averagedSecondMoment H (prior E) hc rho O =
      ((d : ℝ)^2-1)/(d : ℝ)^3 *
        (localityNumerator O / ((d : ℝ)*w-1) +
          ((d : ℝ)^2-1) * ((d : ℝ)*hsSquare O - localityNumerator O) /
            ((d : ℝ)^2-2*(d : ℝ)*w+1)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
