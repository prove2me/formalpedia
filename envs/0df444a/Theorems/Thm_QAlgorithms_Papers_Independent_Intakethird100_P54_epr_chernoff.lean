-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_epr_chernoff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.epr_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:12:32.41643+00:00
-- url     : https://prove2.me/theorems/5e4b5059-ce00-4a05-bad9-8afe22c86b10
-- title:
--   EPR Chernoff coefficient and piecewise optimizer
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Assume $R_1<1$ and $N>0$. Put $T_b=1-R_b$,
--
--   $$\alpha=\frac{T_0N+1}{T_1N+1},\quad\beta=\frac{T_0}{T_1},\quad C=\frac{[(1-r_0r_1)N+1]^2}{T_0N+1},\quad D=T_1N.$$
--
--   Then $1<\alpha<\beta$ and $C>D>0$. For every $s\in[0,1]$, $C\alpha^s-D\beta^s>0$ and the $M$-pair coefficient is
--
--   $$Q_s^{(1)}=(C\alpha^s-D\beta^s)^{-1},\qquad Q_s^{(M)}=(Q_s^{(1)})^M.$$
--
--   Write $d=D\ln\beta-C\ln\alpha$. If $d\ge0$ choose $s_*=0$; otherwise choose
--
--   $$s_*=\min\left\{1,\frac{\ln[(C\ln\alpha)/(D\ln\beta)]}{\ln(\beta/\alpha)}\right\}.$$
--
--   This $s_*\in[0,1]$ attains $Q^{(M)}$ and $P_e\le\tfrac12(C\alpha^{s_*}-D\beta^{s_*})^{-M}$. At $N=0$ the logarithmic optimizer is bypassed: $\mathcal F=Q=1$ and $P_e=1/2$. The ideal-memory endpoint is treated separately.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 9, epr-chernoff

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

/-- EPR Chernoff expression and computed optimizer, PDF pp.9–10, (77)–(88).
The derivative test uses D ln beta-C ln alpha. Ideal memory and N=0 never use
beta=T0/T1 or the logarithmic critical-point expression. -/
theorem epr_chernoff (M : ℕ) (hM : 0 < M) (c : Channels) (hc : ValidSplitters c)
    (hr : Reading c) (hloss : (c true).reflectance < 1) :
    (∀ N : ℝ, 0 < N →
      1 < eprAlpha c N ∧ eprAlpha c N < eprBeta c ∧
      0 < eprD c N ∧ eprD c N < eprC c N ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        0 < eprC c N * Real.rpow (eprAlpha c N) s - eprD c N * Real.rpow (eprBeta c) s ∧
        outputChernoffAt c (tmsvProbe 1 N) s =
          (eprC c N * Real.rpow (eprAlpha c N) s - eprD c N * Real.rpow (eprBeta c) s)⁻¹ ∧
        outputChernoffAt c (tmsvProbe M N) s=(outputChernoffAt c (tmsvProbe 1 N) s)^M) ∧
      eprOptimizer c N ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        outputChernoffAt c (tmsvProbe M N) (eprOptimizer c N) ≤ outputChernoffAt c (tmsvProbe M N) s) ∧
      outputChernoff c (tmsvProbe M N)=outputChernoffAt c (tmsvProbe M N) (eprOptimizer c N) ∧
      outputError c (tmsvProbe M N) ≤ (1/2) *
        (eprC c N * Real.rpow (eprAlpha c N) (eprOptimizer c N) -
          eprD c N * Real.rpow (eprBeta c) (eprOptimizer c N))^(-(M : ℤ))) ∧
    outputFidelity c (tmsvProbe M 0)=1 ∧ outputChernoff c (tmsvProbe M 0)=1 ∧
    outputError c (tmsvProbe M 0)=1/2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
