-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_epr_ideal
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.epr_ideal
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:13:17.954784+00:00
-- url     : https://prove2.me/theorems/b9ca0bb5-0d0d-45f5-a039-c8e858a49b87
-- title:
--   Ideal-memory EPR Chernoff endpoint
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Assume $R_1=1$ and let $M\ge1$ identical EPR pairs each have signal energy $N\ge0$. Then
--
--   $$Q=\mathcal F=[1+(1-r_0)N]^{-2M},\qquad P_e\le\frac12[1+(1-r_0)N]^{-2M}.$$
--
--   The support endpoint $s_*=1$ attains the coefficient and is no larger than $Q_s$ for any $s\in[0,1]$.
--
--   This formula includes the vacuum and does not evaluate the generic undefined ratio $T_0/T_1$ at $T_1=0$.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 10, epr-ideal

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

/-- Ideal-memory EPR endpoint, PDF p.10, (90); optimizer s=1 is a conclusion.
No division by the zero ideal transmission is performed. -/
theorem epr_ideal (M : ℕ) (hM : 0 < M) (c : Channels) (hc : ValidSplitters c)
    (hr : Reading c) (h1 : (c true).reflectance=1) (N : ℝ) (hN : 0 ≤ N) :
    outputChernoff c (tmsvProbe M N)=outputFidelity c (tmsvProbe M N) ∧
    outputChernoff c (tmsvProbe M N)=((1-(c false).r)*N+1)^(-(2*M : ℤ)) ∧
    outputChernoffAt c (tmsvProbe M N) 1=outputChernoff c (tmsvProbe M N) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      outputChernoffAt c (tmsvProbe M N) 1 ≤ outputChernoffAt c (tmsvProbe M N) s) ∧
    outputError c (tmsvProbe M N) ≤ (1/2)*((1-(c false).r)*N+1)^(-(2*M : ℤ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
