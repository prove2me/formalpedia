-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_chernoff_exponent
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.chernoff_exponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:06:03.105673+00:00
-- url     : https://prove2.me/theorems/51bcc0ea-74cc-465e-b609-eade0b9e2389
-- title:
--   Signal-energy bound on the Chernoff exponent
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Assume additionally $R_1<1$, and let a normalized pure probe have finite mean signal energy $N_s$. Then $0<\mu<1$ and $Q(\psi)>0$. With natural logarithms and $\xi=-\ln Q(\psi)$,
--
--   $$\xi\le-2N_s\ln\mu=\ln\bigl(\mu^{-2N_s}\bigr).$$
--
--   For each positive integer $L$, the normalized experiment consisting of $L$ independent copies also satisfies
--
--   $$P_e(\psi^{\otimes L})\ge\frac14\mu^{2N_sL}.$$
--
--   These bounds control copy asymptotics; the identification of $\xi$ with the limiting optimal-error exponent is cited background, equation (55), rather than a new theorem of this paper.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 7, chernoff-exponent

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

/-- Chernoff exponent and finite-copy bound, PDF p.7, (56)–(57).
Natural logarithms are used; R1<1 excludes a log-zero/infinite-exponent endpoint.
The identification with the asymptotic opticalError exponent (55) is cited background [18]. -/
theorem chernoff_exponent {M J : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (hloss : (c true).reflectance < 1)
    (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M))) (hpsi : ‖psi‖=1)
    (N : ℝ) (hN : HasSignalEnergy psi N) :
    0 < splitterOverlap c ∧ splitterOverlap c < 1 ∧ 0 < outputChernoff c psi ∧
    -Real.log (outputChernoff c psi) ≤ -2*N*Real.log (splitterOverlap c) ∧
    ∀ L : ℕ, 0 < L → ‖opticalCopies psi L‖=1 ∧
      Real.rpow (splitterOverlap c) (2*N*(L : ℝ))/4 ≤ outputError c (opticalCopies psi L) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
