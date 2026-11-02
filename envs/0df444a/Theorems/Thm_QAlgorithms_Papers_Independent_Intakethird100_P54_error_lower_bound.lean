-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_error_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.error_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:05:41.259081+00:00
-- url     : https://prove2.me/theorems/c6db97b7-fd1b-418f-ba62-ab37d317909f
-- title:
--   Universal signal-energy lower bound on discrimination error
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   For every normalized pure joint probe with finite mean total signal photon number $N_s\ge0$,
--
--   $$P_e(\psi)\ge\frac{1-\sqrt{1-\mu^{2N_s}}}{2}.$$
--
--   This is a universal lower bound, independent of the numbers of signal and idler modes. At $N_s=0$ both returned states coincide, giving $P_e=1/2$.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 6, error-lower-bound

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

/-- Universal operational error LOWER bound, PDF pp.6–7, (53). N is the finite
mean total SIGNAL photon number, and can be zero or noninteger. -/
theorem error_lower_bound {M J : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M)))
    (hpsi : ‖psi‖=1) (N : ℝ) (hN : HasSignalEnergy psi N) :
    lowerError (Real.rpow (splitterOverlap c) (2*N)) ≤ outputError c psi := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
