-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P20_phase_covariance
-- name    : QAlgorithms.Papers.Independent.Bridge50.P20.phase_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:05:24.994767+00:00
-- url     : https://prove2.me/theorems/d9d15062-bb51-4390-80fd-7ffb7a155e99
-- title:
--   Phase covariance implies invariance of the Choi state
-- statement:
--   Let $\mathcal N$ be a qubit CPTP channel, and let $\sigma_z=\operatorname{diag}(1,-1)$. Suppose, for every real $\theta$ and normalized input state $\rho$, that $\mathcal N(e^{i\theta\sigma_z}\rho e^{-i\theta\sigma_z})=e^{i\theta\sigma_z}\mathcal N(\rho)e^{-i\theta\sigma_z}$. Let $\pi_{\mathcal N}$ be its normalized Choi state and put $U_\theta=e^{i(\theta/2)\sigma_z}\otimes e^{-i(\theta/2)\sigma_z}$. Then
--
--   $$
--   U_\theta\pi_{\mathcal N}U_\theta^\dagger=\pi_{\mathcal N}\quad(0\le\theta\le2\pi),\qquad
--   \frac1{2\pi}\int_0^{2\pi}U_\theta\pi_{\mathcal N}U_\theta^\dagger\,d\theta=\pi_{\mathcal N}.
--   $$
--
--   This identifies a symmetry that can be used in both separable-comparison optimizations.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, PDF p. 27, Appendix B, (B1)–(B3): channel covariance implies Choi invariance

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms QAlgorithms.Entanglement

-- Reuse pinned accepted definitions; source-specific conventions are audited below.

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P53 (amplitudeDamping)

open QAlgorithms.Papers.Independent.Information100.P75 (mixedIdentity)

open QAlgorithms.Papers.Independent.Next46.P29 (zRotation)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1707.05543v2, PDF pp.27-28, (B1)-(B3): covariance implies invariance
of the normalized Choi state, and its normalized angular average equals itself. -/
theorem phase_covariance (N : Superop (Fin 2) (Fin 2))
    (hN : IsChannel N) (hc : IsPhaseCovariant N) :
    IsPhaseInvariant (choiState N) ∧ phaseTwirl (choiState N) = choiState N := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P20

end
