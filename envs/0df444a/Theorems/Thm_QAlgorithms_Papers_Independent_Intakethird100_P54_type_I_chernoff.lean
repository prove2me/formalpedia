-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_type_I_chernoff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.type_I_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:07:29.420425+00:00
-- url     : https://prove2.me/theorems/bb28d885-bd0b-4032-90f3-39788341c1d8
-- title:
--   Fock Chernoff optimality in Type I target detection
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Assume $R_0=0$ and restrict to normalized pure signal-only probes, so there are no retained idlers entangled with the signals. The absent-target return is vacuum and $Q(\psi)=\mathcal F(\psi)$. For a Fock occupation $\mathbf N$ with total $K$,
--
--   $$Q(|\mathbf N\rangle)=(1-R_1)^K\le Q(\psi)$$
--
--   for every such pure signal-only competitor of mean signal energy $K$.
--
--   The restriction makes one returned state pure, which is essential to this Chernoff optimization claim.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 7, type-I-chernoff

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

/-- Type I target detection: pure SIGNAL-ONLY probes, PDF p.7.
The no-entangled-idler restriction is essential to the purity argument. -/
theorem type_I_chernoff {M : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (habsent : (c false).reflectance=0) :
    (∀ psi : Hilbert (Occupation (Fin 0) × Occupation (Fin M)), ‖psi‖=1 →
      returned (c false) psi = opticalPureKernel (fock (0 : Occupation (Fin M))) ∧
      outputChernoff c psi=outputFidelity c psi) ∧
    (∀ n : Occupation (Fin M),
      outputChernoff c (fock n) = (1-(c true).reflectance)^photons n ∧
      ∀ psi : Hilbert (Occupation (Fin 0) × Occupation (Fin M)),
        ‖psi‖=1 → HasSignalEnergy psi (photons n : ℝ) →
          outputChernoff c (fock n) ≤ outputChernoff c psi) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
