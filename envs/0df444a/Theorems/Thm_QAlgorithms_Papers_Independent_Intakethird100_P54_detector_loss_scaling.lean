-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_detector_loss_scaling
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.detector_loss_scaling
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:13:46.642413+00:00
-- url     : https://prove2.me/theorems/57fbfd04-8612-4d71-a394-41688f28c10c
-- title:
--   Uniform vacuum detector loss scales the effective reflectances
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Let an independent uniform vacuum attenuator with efficiency $\eta\in[0,1]$ act on each returned signal mode while every idler is retained. For the paper's Fock and product coherent probes, the returned state is precisely that for effective reflectances
--
--   $$R_b^{\rm eff}=\eta R_b,\qquad T_b^{\rm eff}=1-\eta R_b.$$
--
--   Thus the Fock optimum is the binomial counting error at these effective reflectances. A product coherent probe of signal energy $N_s$ has exact error
--
--   $$P_e^{\rm eff}=\frac{1-\sqrt{1-e^{-\eta(r_1-r_0)^2N_s}}}{2}.$$
--
--   Zero efficiency yields identical returned signals and error $1/2$. The assertion concerns common independent vacuum loss; it does not extend the paper's analysis to thermal noise, dark counts or an experimentally specified EPR receiver.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 12, detector-loss-scaling

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

/-- Uniform vacuum detector loss for the source's Fock and coherent transmitters,
PDF p.12, IV.E.2. Effective reflectances are eta R_b, including eta=0; there is
no assertion about thermal noise, dark counts or an implementable EPR receiver. -/
theorem detector_loss_scaling {M J : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    (∀ (n : Occupation (Fin M)) (b : Bool),
      attenuate (vacuumEfficiency eta h0 h1) (returned (c b) (fock n)) =
        returned (efficiencyScaled (c b) eta h0 h1) (fock n)) ∧
    (∀ n : Occupation (Fin M),
      opticalError (attenuate (vacuumEfficiency eta h0 h1) (returned (c false) (fock n)))
        (attenuate (vacuumEfficiency eta h0 h1) (returned (c true) (fock n))) =
          countingError (fun b => efficiencyScaled (c b) eta h0 h1) (photons n)) ∧
    (∀ (beta : Fin J → ℂ) (alpha : Fin M → ℂ) (b : Bool),
      attenuate (vacuumEfficiency eta h0 h1) (returned (c b) (coherentOpticalProbe beta alpha)) =
        returned (efficiencyScaled (c b) eta h0 h1) (coherentOpticalProbe beta alpha)) ∧
    (∀ (beta : Fin J → ℂ) (alpha : Fin M → ℂ),
      opticalError (attenuate (vacuumEfficiency eta h0 h1) (returned (c false) (coherentOpticalProbe beta alpha)))
        (attenuate (vacuumEfficiency eta h0 h1) (returned (c true) (coherentOpticalProbe beta alpha))) =
          lowerError (Real.exp (-eta*coherentExponent c*coherentEnergy alpha))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
