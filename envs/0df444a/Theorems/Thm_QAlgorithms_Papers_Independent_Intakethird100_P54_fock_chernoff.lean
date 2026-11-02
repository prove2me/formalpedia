-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_fock_chernoff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.fock_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:10:09.891178+00:00
-- url     : https://prove2.me/theorems/ca46feb0-cd57-40be-b44e-bb354f397901
-- title:
--   Explicit Fock Chernoff optimizer and exponent
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Assume $0<R_0<R_1<1$, and let a Fock probe have total photon number $K\in\mathbb N$. Put $T_b=1-R_b$, $f(s)=R_0^sR_1^{1-s}+T_0^sT_1^{1-s}$, and
--
--   $$s_*=\frac{\ln[-R_1\ln(R_0/R_1)/(T_1\ln(T_0/T_1))]}{\ln[T_0R_1/(T_1R_0)]}.$$
--
--   Then $s_*\in[0,1]$ minimizes $f$, $Q_s=f(s)^K$, and
--
--   $$Q=f(s_*)^K=e^{-\xi_{\rm Num}K},\qquad P_e\le\frac12f(s_*)^K,\qquad\xi_{\rm Num}=-\ln f(s_*).$$
--
--   The per-photon gain is defined by $G=\xi_{\rm Num}/\xi_{\rm CS}$ with $\xi_{\rm CS}=(r_1-r_0)^2$. It is not asserted to be large for all channels. At $K=0$, $Q=1$.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 8, fock-chernoff

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

/-- Number-state Chernoff bound and derived optimizer, PDF p.8, (66)–(69).
The gain is a defined per-photon ratio, not a universal large-gain claim. -/
theorem fock_chernoff {M : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (h0 : 0 < (c false).reflectance)
    (h1 : (c true).reflectance < 1) (n : Occupation (Fin M)) :
    fockOptimizer c ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      outputChernoffAt c (fock n) s=(fockCoefficient c s)^photons n ∧
      fockCoefficient c (fockOptimizer c) ≤ fockCoefficient c s) ∧
    outputChernoff c (fock n)=(fockCoefficient c (fockOptimizer c))^photons n ∧
    outputError c (fock n) ≤ (fockCoefficient c (fockOptimizer c))^photons n/2 ∧
    (fockCoefficient c (fockOptimizer c))^photons n =
      Real.exp (-numberExponent c*(photons n : ℝ)) ∧
    exponentGain c=numberExponent c/coherentExponent c := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
