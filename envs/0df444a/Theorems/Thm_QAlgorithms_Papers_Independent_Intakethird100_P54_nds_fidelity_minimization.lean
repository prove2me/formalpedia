-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_nds_fidelity_minimization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.nds_fidelity_minimization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:04:27.865187+00:00
-- url     : https://prove2.me/theorems/c75eeca8-2857-42db-928b-98a0ecb43c62
-- title:
--   NDS fidelity minimization at a prescribed photon law
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   Let $|\psi\rangle$ be any normalized pure NDS probe, and let $p_n$ be its total signal photon law. Then
--
--   $$\mathcal F(\psi)=\left(\sum_{n=0}^\infty p_n\mu^n\right)^2\le\mathcal F(\phi)$$
--
--   for every normalized pure competitor $|\phi\rangle$ with the same total law, allowing any finite number of retained idler modes. In addition, every probability law on multimode signal occupations is realized by a normalized NDS purification with one freely chosen optical idler.
--
--   Thus the bound is attained at a prescribed total law, in particular when the entire multimode occupation law is fixed; no adequate purification is postulated in an arbitrarily small prescribed idler space.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 6, nds-fidelity-minimization

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

/-- NDS probes minimize fidelity at fixed TOTAL signal photon law, PDF p.6, (48).
Comparators have arbitrary finite idler count. Realizability is asserted with a freely
chosen single optical idler, rather than a possibly inadequate prescribed idler. -/
theorem nds_fidelity_minimization {M J : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M)))
    (hpsi : ‖psi‖ = 1) (hnds : IsNDS psi) :
    outputFidelity c psi = (∑' n : ℕ, totalLaw psi n * (splitterOverlap c)^n)^2 ∧
    (∀ (Jother : ℕ) (other : Hilbert (Occupation (Fin Jother) × Occupation (Fin M))),
      ‖other‖ = 1 → totalLaw other = totalLaw psi →
        outputFidelity c psi ≤ outputFidelity c other) ∧
    (∀ p : Occupation (Fin M) → ℝ, (∀ n, 0 ≤ p n) → Summable p → (∑' n, p n)=1 →
      ∃ z : Hilbert (Occupation (Fin 1) × Occupation (Fin M)),
        ‖z‖=1 ∧ IsNDS z ∧ signalLaw z=p) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
