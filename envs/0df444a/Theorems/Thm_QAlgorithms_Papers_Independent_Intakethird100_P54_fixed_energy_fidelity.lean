-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_fixed_energy_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.fixed_energy_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:04:51.182335+00:00
-- url     : https://prove2.me/theorems/2c81b9cc-82f2-4017-9182-e9a13d41b490
-- title:
--   Universal energy fidelity bound and integer Fock attainment
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Every normalized pure joint probe of finite mean total signal energy $N_s\ge0$ obeys
--
--   $$\mathcal F(\psi)\ge\mu^{2N_s}.$$
--
--   For each multimode occupation vector $\mathbf N$, write $K=\sum_mN_m\in\mathbb N$. Its Fock probe has mean signal energy $K$ and
--
--   $$\mathcal F(|\mathbf N\rangle)=\mu^{2K}.$$
--
--   It therefore attains the universal bound at every integer energy. The convention $0^0=1$ includes the vacuum and opposite ideal channel endpoints. This statement does not identify all minimizers or assert error-probability optimality.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 6, fixed-energy-fidelity

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

/-- Universal real-energy fidelity lower bound and INTEGER-energy Fock attainment,
PDF p.6, (49)–(52). No false uniqueness assertion is included. The opposite ideal
endpoints use Real.rpow 0 0=1; no noninteger Fock occupation is postulated. -/
theorem fixed_energy_fidelity {M : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) :
    (∀ (J : ℕ) (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M))) (N : ℝ),
      ‖psi‖=1 → HasSignalEnergy psi N → Real.rpow (splitterOverlap c) (2*N) ≤ outputFidelity c psi) ∧
    (∀ n : Occupation (Fin M), HasSignalEnergy (fock n) (photons n : ℝ) ∧
      outputFidelity c (fock n) = Real.rpow (splitterOverlap c) (2*(photons n : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
