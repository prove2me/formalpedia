-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_averagedSecondMoment_entanglementFeatures
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.averagedSecondMoment_entanglementFeatures
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:01:39.246184+00:00
-- url     : https://prove2.me/theorems/baf0e6f3-f6f5-4733-8a2d-7b2b148dbb63
-- title:
--   Local-state averaged second moment from second entanglement features
-- statement:
--   Let $\nu$ be the locally scrambled prior of a complete projective experiment on $N$ qudits, $d\ge2$, with reconstruction coefficients $r$ solving Eq. (12). Fix a density matrix $\rho$ and a traceless Hermitian $O$. Let $H$ be normalized Haar measure on $U(d)^N$, $W_C=\mathbb E_\nu\operatorname{Tr}[(\operatorname{Tr}_{\bar C}S)^2]$, and $W_{O,D}=\mathbb E_{V\sim H}\operatorname{Tr}[(\operatorname{Tr}_{\bar D}(V^\dagger OV))^2]$. The local-state average $Q_{\mathrm{av}}(O)=\mathbb E_{V\sim H}Q_{V^\dagger\rho V}(O)$ equals the prior second moment of the prediction and satisfies
--
--   $$Q_{\mathrm{av}}(O)=\sum_{A,B,C,D}v_{A,B,C,D}W_{A\cap B\cap C}W_{O,D},$$
--
--   $$v_{A,B,C,D}=r_A r_B\left(\frac{d^2}{d^2-1}\right)^N\frac{d^{|A\cap B\cap C|}}{d^{|C|}}\left(-\frac1d\right)^{|C\triangle D|}.$$
--
--   All indices are arbitrary regions, including empty and full regions. Observable partial traces are unnormalized. This formula removes the input-state dependence by averaging; it gives no pointwise bound for each $\rho$.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 5, §II B / Appendix B: state-averaged second moment in entanglement features

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

/-- PDF p.5 Eqs.(20)–(22), Appendix B pp.18–19: local-state averaged Q in
second EFs. The signed power is multiplicative. This is an average, not a
pointwise-in-rho variance bound. -/
theorem averagedSecondMoment_entanglementFeatures {n d : ℕ} (hd : 2 ≤ d)
    (E : ProjectiveEnsemble n d) (hls : LocallyScrambled (prior E)) (hc : Complete (prior E))
    (H : Measure (Local n d)) [IsProbabilityMeasure H] [H.IsMulLeftInvariant]
    (rho O : Op n d) (hrho : IsDensityMatrix rho) (hO : O.IsHermitian) (ht : O.trace = 0)
    (r : Finset (Fin n) → ℝ) (hr : CoefficientSystem (prior E) r) :
    averagedSecondMoment H (prior E) hc rho O =
      (∫ S, shadowEstimate (prior E) hc O S ^ 2 ∂prior E) ∧
    averagedSecondMoment H (prior E) hc rho O =
      ∑ A : Finset (Fin n), ∑ B : Finset (Fin n), ∑ C : Finset (Fin n), ∑ D : Finset (Fin n),
        varianceCoefficient d r A B C D * feature (prior E) (A ∩ B ∩ C) *
          observableFeature H O D := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
