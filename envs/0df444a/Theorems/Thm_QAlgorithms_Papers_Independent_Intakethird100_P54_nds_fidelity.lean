-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_nds_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.nds_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:02:52.863189+00:00
-- url     : https://prove2.me/theorems/be69f34f-ac5a-4b79-af10-795c1b850bec
-- title:
--   NDS fidelity as the squared sum of sector overlap magnitudes
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections.
--
--   For a normalized pure NDS probe with multimode signal law $p_{\mathbf n}$, use the source amplitudes
--   $A_{\mathbf n;\mathbf k}^{(b)}=\prod_m\sqrt{\binom{n_m}{k_m}}e^{in_m\theta_b}r_b^{n_m-k_m}t_b^{k_m}$ when $\mathbf k\le\mathbf n$, and zero otherwise. The overlap series and its outer absolute-value sum converge, and
--
--   $$I_{\mathbf k}=\sum_{\mathbf n}p_{\mathbf n}\overline{A_{\mathbf n;\mathbf k}^{(0)}}A_{\mathbf n;\mathbf k}^{(1)},\qquad \mathcal F=\left(\sum_{\mathbf k}|I_{\mathbf k}|\right)^2\ge\left|\sum_{\mathbf k}I_{\mathbf k}\right|^2=O(\psi).$$
--
--   This exact formula can improve the general bound, with equality permitted even when the channel phases differ.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 5, nds-fidelity

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

/-- NDS fidelity with inner absolute values and a squared outer sum, PDF pp.5–6,
(30)–(31),(43)–(44). Comparison with the general bound is non-strict. -/
theorem nds_fidelity {M J : ℕ} (hM : 0 < M) (c : Channels) (hc : ValidSplitters c)
    (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M))) (hpsi : ‖psi‖ = 1)
    (hnds : IsNDS psi) :
    (∀ k, Summable (lossOverlapTerm c psi k) ∧
      lossOverlap c psi k = ∑' n, lossOverlapTerm c psi k n) ∧
    Summable (fun k => ‖lossOverlap c psi k‖) ∧
    Summable (lossOverlap c psi) ∧
    outputFidelity c psi = (∑' k, ‖lossOverlap c psi k‖)^2 ∧
    Complex.normSq (∑' k, lossOverlap c psi k) = purificationOverlap c psi ∧
    purificationOverlap c psi ≤ outputFidelity c psi := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
