-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_fock_target_error
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.fock_target_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:10:36.393203+00:00
-- url     : https://prove2.me/theorems/ce15f06e-64dd-4b2c-9756-cc0945c39422
-- title:
--   Exact Fock target-detection error
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Assume $R_0=0$. For any multimode Fock occupation with total signal photon number $K$,
--
--   $$P_e=\frac12(1-R_1)^K.$$
--
--   Photon counting with decision 'present' exactly when the total returned count is positive attains this error. At $K=0$ it always declares absence and has error $1/2$; at $R_1=1$ and $K>0$ the error is zero.
--
--   This gives an exact endpoint rule without a logarithmic threshold.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 9, fock-target-error

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P54

noncomputable section

open scoped BigOperators ComplexConjugate

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P54

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Exact Fock target-detection error and attaining count>0 rule, PDF p.9, (70).
K=0 is a tie with opticalError 1/2; the endpoint R1=1 is included. -/
theorem fock_target_error {M : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (h0 : (c false).reflectance=0)
    (n : Occupation (Fin M)) :
    outputError c (fock n)=(1-(c true).reflectance)^photons n/2 ∧
    ∃ E, IsOpticalEffect E ∧ CountsAs E (fun q => decide (0 < photons q)) ∧
      sectorRisk c (fock n) E (1/2) (1/2)=outputError c (fock n) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
