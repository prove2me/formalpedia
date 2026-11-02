-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_coherent_error
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.coherent_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:08:16.002524+00:00
-- url     : https://prove2.me/theorems/1d8fb217-6266-4084-8f61-2174f9bf652d
-- title:
--   Exact coherent-state error and Chernoff coefficient
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Let the signal coherent amplitudes be $\alpha_m\in\mathbb C$ and the retained idler amplitudes be arbitrary. The full product coherent probe is normalized and has signal energy $N_s=\sum_m|\alpha_m|^2$. Then
--
--   $$\mathcal F=Q=e^{-(r_1-r_0)^2N_s},\qquad P_e=\frac{1-\sqrt{1-e^{-(r_1-r_0)^2N_s}}}{2}\le\frac12e^{-(r_1-r_0)^2N_s}.$$
--
--   The result depends only on total signal energy, not its distribution among modes. The real field difference is appropriate because the channel phases are aligned.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 7, coherent-error

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

/-- Coherent-state exact error, fidelity and Chernoff coefficient, PDF pp.7–8,
(61),(68), with multimode invariance from footnote [6], p.13. Section IV has
Delta=0; the real field-magnitude difference is therefore legitimate. -/
theorem coherent_error {M J : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (beta : Fin J → ℂ) (alpha : Fin M → ℂ) :
    ‖coherentOpticalProbe beta alpha‖=1 ∧ HasSignalEnergy (coherentOpticalProbe beta alpha) (coherentEnergy alpha) ∧
    outputFidelity c (coherentOpticalProbe beta alpha) = Real.exp (-coherentExponent c * coherentEnergy alpha) ∧
    outputChernoff c (coherentOpticalProbe beta alpha) = Real.exp (-coherentExponent c * coherentEnergy alpha) ∧
    outputError c (coherentOpticalProbe beta alpha) =
      lowerError (Real.exp (-coherentExponent c * coherentEnergy alpha)) ∧
    outputError c (coherentOpticalProbe beta alpha) ≤ Real.exp (-coherentExponent c * coherentEnergy alpha)/2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
