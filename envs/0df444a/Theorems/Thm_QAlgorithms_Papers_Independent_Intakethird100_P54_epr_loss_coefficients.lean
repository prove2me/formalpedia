-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_epr_loss_coefficients
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.epr_loss_coefficients
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:11:30.215267+00:00
-- url     : https://prove2.me/theorems/bba6df4f-f9ed-4d58-b8ed-ff4a5a0c87f7
-- title:
--   EPR geometric loss probabilities and sector overlaps
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   For one signal-idler pair and per-pair signal energy $N\ge0$, the normalized NDS state is
--
--   $$|\psi_N\rangle=\sqrt{\frac1{N+1}}\sum_{n=0}^\infty\left(\sqrt{\frac N{N+1}}\right)^n|n\rangle_I|n\rangle_S.$$
--
--   Its mean signal energy is $N$. The actual loss probability and overlap, with convergent defining series, satisfy
--
--   $$p_k^{(b)}=\frac{(T_bN)^k}{(T_bN+1)^{k+1}},\qquad I_k=\frac{(t_0t_1N)^k}{[(1-r_0r_1)N+1]^{k+1}},\quad T_b=1-R_b.$$
--
--   The integer powers give $p_0^{(b)}=I_0=1$ at $N=0$ and all positive-loss sectors vanish. This is the sector data for the EPR fidelity and Chernoff formulas.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 9, epr-loss-coefficients

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

/-- EPR geometric loss probabilities and loss-sector overlap, PDF p.9, (73)–(75).
N is per-pair signal energy, not total energy of a multipair probe. -/
theorem epr_loss_coefficients (c : Channels) (hc : ValidSplitters c) (hr : Reading c)
    (N : ℝ) (hN : 0 ≤ N) :
    Memℓp (tmsvCoefficients 1 N) 2 ∧ ‖tmsvProbe 1 N‖=1 ∧
    HasSignalEnergy (tmsvProbe 1 N) N ∧ IsNDS (tmsvProbe 1 N) ∧
    (∀ b k, lossProbability c (tmsvProbe 1 N) b (fun _ => k)=
      (((1-(c b).reflectance)*N)^k / ((1-(c b).reflectance)*N+1)^(k+1))) ∧
    (∀ k, Summable (lossOverlapTerm c (tmsvProbe 1 N) (fun _ => k)) ∧
      lossOverlap c (tmsvProbe 1 N) (fun _ => k)=
        (((c false).t*(c true).t*N)^k / ((1-(c false).r*(c true).r)*N+1)^(k+1) : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
