-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_target_detection_no_go
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.target_detection_no_go
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:06:56.880842+00:00
-- url     : https://prove2.me/theorems/590686f3-fbd3-4ee8-a4d9-ce5134f6ffc8
-- title:
--   Zero-background target envelopes and fixed-energy high-loss limit
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Assume $R_0=0$ and fix a finite $N_s\ge0$. For $R=R_1$, define
--
--   $$L(R,N_s)=\frac{1-\sqrt{1-(1-R)^{N_s}}}{2},\qquad C(R,N_s)=\frac{1-\sqrt{1-e^{-RN_s}}}{2}.$$
--
--   Every normalized pure joint probe of signal energy $N_s$ has error at least $L(R_1,N_s)$. Every product coherent probe with that signal energy, with arbitrary pure coherent idlers, has exact error $C(R_1,N_s)$. For each fixed $N_s$,
--
--   $$\lim_{R\downarrow0}\bigl(C(R,N_s)-L(R,N_s)\bigr)=0,\qquad\lim_{R\downarrow0}\frac{-\ln(1-R)}R=1.$$
--
--   These precise envelopes express the paper's high-loss comparison without a tolerance for 'appreciable' or a uniform relative-error claim at unbounded energy. The background environment is vacuum.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 7, target-detection-no-go

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

/-- Exact zero-background target envelopes and their fixed-energy high-loss limit,
PDF p.7, (59)–(60). The prose 'appreciable' is given no invented uniform tolerance. -/
theorem target_detection_no_go {M J : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (habsent : (c false).reflectance=0)
    (N : ℝ) (hN : 0 ≤ N) :
    (∀ psi : Hilbert (Occupation (Fin J) × Occupation (Fin M)), ‖psi‖=1 → HasSignalEnergy psi N →
      targetLower (c true).reflectance N ≤ outputError c psi) ∧
    (∀ (beta : Fin J → ℂ) (alpha : Fin M → ℂ), coherentEnergy alpha=N →
      outputError c (coherentOpticalProbe beta alpha) = targetCoherent (c true).reflectance N) ∧
    Tendsto (fun R : ℝ => targetCoherent R N - targetLower R N)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Tendsto (fun R : ℝ => -Real.log (1-R)/R)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
