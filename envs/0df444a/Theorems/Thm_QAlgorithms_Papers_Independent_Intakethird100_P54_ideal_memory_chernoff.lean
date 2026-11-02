-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_ideal_memory_chernoff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.ideal_memory_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:06:25.743278+00:00
-- url     : https://prove2.me/theorems/9a5d27da-1d69-4d94-9798-8ece993c2d33
-- title:
--   Fock optimality for the ideal-memory Chernoff coefficient
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Assume $R_1=1$. For every normalized pure joint probe, including arbitrary finite retained idlers, $\rho_1=|\psi\rangle\langle\psi|$ and
--
--   $$Q(\psi)=\mathcal F(\psi),\qquad P_e(\psi)\le\frac{\mathcal F(\psi)}2.$$
--
--   Every Fock occupation with total photon number $K\in\mathbb N$ attains $Q=R_0^K$, which is no larger than the Chernoff coefficient of any normalized pure joint probe of mean signal energy $K$.
--
--   This is optimality of the Chernoff bound, distinguished from a general minimum-error assertion.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 7, ideal-memory-chernoff

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

/-- Ideal-memory Chernoff optimality for all pure idler-assisted competitors,
PDF p.7, (58). Integer-energy Fock probes attain the smallest coefficient;
no general minimum-opticalError optimality is claimed here. -/
theorem ideal_memory_chernoff {M : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (hideal : (c true).reflectance=1) :
    (∀ (J : ℕ) (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M))), ‖psi‖=1 →
      returned (c true) psi = opticalPureKernel psi ∧
      outputChernoff c psi = outputFidelity c psi ∧
      outputError c psi ≤ outputFidelity c psi/2) ∧
    (∀ n : Occupation (Fin M),
      outputChernoff c (fock n) = (c false).reflectance ^ photons n ∧
      ∀ (J : ℕ) (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M))),
        ‖psi‖=1 → HasSignalEnergy psi (photons n : ℝ) →
          outputChernoff c (fock n) ≤ outputChernoff c psi) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
