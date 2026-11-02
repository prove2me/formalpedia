-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_product_laws
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.product_laws
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:03:54.990063+00:00
-- url     : https://prove2.me/theorems/8f81ff65-5db0-4834-96eb-6e3d2135c79f
-- title:
--   Fidelity and common-exponent Chernoff product laws
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections.
--
--   Let $|\Psi\rangle=\bigotimes_{m=1}^M|\psi_m\rangle$, where each normalized pure factor has one signal mode and an arbitrary finite retained idler register. The factors need not be identical or NDS. The grouped product is normalized, and for each common $s\in[0,1]$,
--
--   $$\mathcal F(\Psi)=\prod_{m=1}^M\mathcal F(\psi_m),\qquad Q_s(\Psi)=\prod_{m=1}^M Q_s(\psi_m).$$
--
--   These identities reduce a product experiment to its individual factors. They do not assert multiplicativity after independently minimizing the exponent in each factor.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 6, product-laws

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

/-- Product laws for arbitrary, possibly different and non-NDS, pure factors,
PDF p.6, (46)–(47). The same s is used in every factor; optimized coefficients
are not asserted to multiply. Equation (47)'s missing factor subscript is restored. -/
theorem product_laws {M : ℕ} (hM : 0 < M) (c : Channels) (hc : ValidSplitters c)
    (J : Fin M → ℕ) (psi : ∀ m, Hilbert (Occupation (Fin (J m)) × Occupation (Fin 1)))
    (hpsi : ∀ m, ‖psi m‖ = 1) :
    ‖productOpticalProbe J psi‖ = 1 ∧
    outputFidelity c (productOpticalProbe J psi) = ∏ m, outputFidelity c (psi m) ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      outputChernoffAt c (productOpticalProbe J psi) s = ∏ m, outputChernoffAt c (psi m) s := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
