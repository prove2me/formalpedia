-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_general_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.general_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:01:41.228194+00:00
-- url     : https://prove2.me/theorems/2985e089-aaa4-4d89-9c3c-469a4ab169b9
-- title:
--   General pure-probe fidelity and error lower bounds
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections.
--
--   Let $\lvert\psi\rangle$ be any normalized pure joint probe, with total signal photon law $p_n$, and set $\Delta=\theta_1-\theta_0$ and $\mu=r_0r_1+t_0t_1$. Its loss-sector amplitudes are square summable, $\sum_n p_n=1$, and the following complex series is absolutely convergent:
--
--   $$O(\psi)=\left|\sum_{n=0}^\infty p_n e^{in\Delta}\mu^n\right|^2\le\mathcal F(\psi),\qquad \frac{1-\sqrt{1-O(\psi)}}2\le P_e(\psi).$$
--
--   This lower bound applies without a finite-energy assumption or any restriction on idler correlations.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 1, general-fidelity

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

/-- General fidelity bound and its operational error consequence, PDF pp.3–4,
(11)–(20). No finite-energy or signal-idler orthogonality hypothesis is imposed. -/
theorem general_fidelity {M J : ℕ} (hM : 0 < M) (c : Channels) (hc : ValidSplitters c)
    (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M))) (hpsi : ‖psi‖ = 1) :
    (∀ b k, Memℓp (sectorCoefficients (c b) psi k) 2) ∧
    Summable (totalLaw psi) ∧ (∑' n, totalLaw psi n) = 1 ∧
    Summable (purificationOverlapTerm c psi) ∧
    purificationOverlap c psi ≤ outputFidelity c psi ∧
    lowerError (purificationOverlap c psi) ≤ outputError c psi := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
