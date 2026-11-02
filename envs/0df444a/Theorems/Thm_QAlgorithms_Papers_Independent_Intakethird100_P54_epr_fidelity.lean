-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_epr_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.epr_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:12:04.669024+00:00
-- url     : https://prove2.me/theorems/c7d14c0a-70d5-445b-b4e4-6fa82e154216
-- title:
--   Multipair EPR fidelity and lower error bound
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Let $M\ge1$ identical EPR pairs each have signal energy $N\ge0$. Their product is normalized and has total mean signal energy $N_s=MN$. Then
--
--   $$\mathcal F=[1+(1-\mu)N]^{-2M},\qquad P_e\ge\frac{1-\sqrt{1-[1+(1-\mu)N]^{-2M}}}{2}.$$
--
--   The one-pair case is equation (76). The error expression is a lower bound, with its factor $1/2$, and is not an exact error formula for EPR probes.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 10, epr-fidelity

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

/-- Multipair EPR fidelity and LOWER error bound, PDF pp.9–10, (76),(87),(91).
The prior factor 1/2 is included in lowerError; this is not an exact EPR opticalError formula. -/
theorem epr_fidelity (M : ℕ) (hM : 0 < M) (c : Channels) (hc : ValidSplitters c)
    (hr : Reading c) (N : ℝ) (hN : 0 ≤ N) :
    Memℓp (tmsvCoefficients M N) 2 ∧ ‖tmsvProbe M N‖=1 ∧
    HasSignalEnergy (tmsvProbe M N) ((M : ℝ)*N) ∧
    outputFidelity c (tmsvProbe M N)=((1-splitterOverlap c)*N+1)^(-(2*M : ℤ)) ∧
    lowerError (((1-splitterOverlap c)*N+1)^(-(2*M : ℤ))) ≤ outputError c (tmsvProbe M N) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
