-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_fock_ideal_error
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.fock_ideal_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:11:02.797459+00:00
-- url     : https://prove2.me/theorems/bb5a162e-097a-4172-90d9-8bd56b6e0301
-- title:
--   Corrected exact Fock ideal-memory error
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Assume $R_1=1$. For any multimode Fock occupation with total signal photon number $K$,
--
--   $$P_e=\frac12R_0^K=\frac{\mathcal F}{2}=\frac Q2.$$
--
--   Photon counting followed by decision one exactly when the total returned count equals $K$ is optimal, including the $K=0$ tie.
--
--   **Source correction.** Printed equation (71) contains an extraneous $\ln$ before $1/2$. The counting rule and the next paragraph's equality $P_e=\mathcal F/2$ force the displayed correction; the printed formula would be negative. Independent moderation of this correction remains required.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 9, fock-ideal-error

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

/-- Exact Fock ideal-memory error, PDF p.9, (71)–(72). SOURCE CORRECTION:
printed (71) has an extraneous 'ln' before 1/2. It is deleted here because the
printed counting rule and the following equality Pe=F/2 force R0^K/2; a logarithm
would make a probability negative. Preserve the printed formula in items/HARD. -/
theorem fock_ideal_error {M : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (h1 : (c true).reflectance=1)
    (n : Occupation (Fin M)) :
    outputError c (fock n)=(c false).reflectance^photons n/2 ∧
    outputError c (fock n)=outputFidelity c (fock n)/2 ∧
    outputError c (fock n)=outputChernoff c (fock n)/2 ∧
    ∃ E, IsOpticalEffect E ∧ CountsAs E (fun q => decide (photons q=photons n)) ∧
      sectorRisk c (fock n) E (1/2) (1/2)=outputError c (fock n) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
