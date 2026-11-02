-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_classical_optimum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.classical_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:08:45.411179+00:00
-- url     : https://prove2.me/theorems/5b55852f-30b2-44e9-a8da-014a3d000992
-- title:
--   Pure coherent probes attain the classical optimum
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Let $\nu$ be any probability measure on joint signal and idler coherent amplitudes. Allow arbitrary classical correlations, including Dirac masses. Suppose the signal energy $\sum_m|\alpha_m|^2$ is integrable and its $\nu$-mean is $N_s\ge0$. The corresponding classical mixture satisfies
--
--   $$P_e(\nu)\ge\frac{1-\sqrt{1-e^{-(r_1-r_0)^2N_s}}}{2}.$$
--
--   A pure product coherent probe of signal energy $N_s$ attains equality. No constraint is placed on idler energy.
--
--   This classical optimum combines the coherent error formula with the bound explicitly credited to Theorem 1 of reference [3]. It concerns vacuum background.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 8, classical-optimum

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

/-- Optimal classical performance, PDF p.8, combining (61) with the explicitly
cited Theorem 1 of [3]. Arbitrary correlated coherentOpticalProbe-lossAmplitude probability measures
and Dirac masses are included; only mean SIGNAL energy is constrained. -/
theorem classical_optimum {M J : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c)
    (nu : Measure ((Fin J → ℂ) × (Fin M → ℂ))) [IsProbabilityMeasure nu]
    (N : ℝ) (hN : 0 ≤ N) (hint : Integrable (fun a => coherentEnergy a.2) nu)
    (henergy : (∫ a, coherentEnergy a.2 ∂nu)=N) :
    lowerError (Real.exp (-coherentExponent c*N)) ≤
      opticalError (classicalReturned (c false) nu) (classicalReturned (c true) nu) ∧
    ∃ (beta : Fin J → ℂ) (alpha : Fin M → ℂ), coherentEnergy alpha=N ∧
      outputError c (coherentOpticalProbe beta alpha)=lowerError (Real.exp (-coherentExponent c*N)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
