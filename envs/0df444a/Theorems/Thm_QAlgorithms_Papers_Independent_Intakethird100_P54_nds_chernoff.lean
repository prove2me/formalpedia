-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_nds_chernoff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.nds_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:03:34.383066+00:00
-- url     : https://prove2.me/theorems/77902fb2-07c3-4cf6-bba0-f0438d797f1d
-- title:
--   NDS Chernoff coefficients including support endpoints
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections.
--
--   For a normalized pure NDS probe, let $p_{b,\mathbf k}$ and $I_{\mathbf k}$ denote its actual loss-sector probabilities and overlaps. For every common exponent $s\in[0,1]$ the following series converges:
--
--   $$Q_s=\sum_{\mathbf k:\,p_{0,\mathbf k}p_{1,\mathbf k}>0}p_{0,\mathbf k}^{s-1}p_{1,\mathbf k}^{-s}|I_{\mathbf k}|^2,\qquad P_e\le\frac{Q_s}{2}.$$
--
--   Sectors with either probability zero contribute zero. There exists $s_*\in[0,1]$ attaining $Q=Q_{s_*}$, and $P_e\le Q/2$. In particular, endpoint powers are support projections, so the formula does not replace $Q_0$ or $Q_1$ by one.
--
--   The expression yields computable Chernoff bounds from the same NDS sector data used for exact discrimination.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 6, nds-chernoff

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

/-- NDS Chernoff-type formula with support endpoints and omitted empty sectors,
PDF p.6, (45), together with (7)–(9). The optimizer is concluded, not assumed. -/
theorem nds_chernoff {M J : ℕ} (hM : 0 < M) (c : Channels) (hc : ValidSplitters c)
    (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M))) (hpsi : ‖psi‖ = 1)
    (hnds : IsNDS psi) :
    (∀ s ∈ Set.Icc (0 : ℝ) 1, Summable (ndsChernoffTerm c psi s) ∧
      outputChernoffAt c psi s = ∑' k, ndsChernoffTerm c psi s k ∧
      outputError c psi ≤ outputChernoffAt c psi s / 2) ∧
    (∃ s ∈ Set.Icc (0 : ℝ) 1, outputChernoff c psi = outputChernoffAt c psi s ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, outputChernoffAt c psi s ≤ outputChernoffAt c psi t) ∧
    outputError c psi ≤ outputChernoff c psi / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
