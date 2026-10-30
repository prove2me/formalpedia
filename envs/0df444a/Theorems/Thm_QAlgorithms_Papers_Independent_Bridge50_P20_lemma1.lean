-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P20_lemma1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P20.lemma1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:06:15.142346+00:00
-- url     : https://prove2.me/theorems/078cac7f-df96-4ea6-9b4d-b015d0252ebc
-- title:
--   Twirling preserves an optimal separable comparison state
-- statement:
--   Let $\rho$ be any normalized two-qubit state invariant under $U_\theta=e^{i(\theta/2)\sigma_z}\otimes e^{-i(\theta/2)\sigma_z}$ for $0\le\theta\le2\pi$. Choose either of the feasible sets consisting of all normalized separable states, or those additionally satisfying $\operatorname{Tr}_B\sigma=I/2$. Let $\sigma_*$ be an actual minimizer of $D_{\max}(\rho\Vert\sigma)$ in the chosen feasible set, and define $\overline\sigma_*=(2\pi)^{-1}\int_0^{2\pi}U_\theta\sigma_*U_\theta^\dagger\,d\theta$. Then
--
--   $$
--   \overline\sigma_*\in\mathrm{SEP},\qquad
--   D_{\max}(\rho\Vert\sigma_*)=D_{\max}(\rho\Vert\overline\sigma_*).
--   $$
--
--   In the constrained case, also $\operatorname{Tr}_B\overline\sigma_*=I/2$. Each feasible-set choice has its own supplied optimizer. The input need not be the Choi state of an amplitude-damping channel.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, PDF p. 28, Appendix B, Lemma 1, (B4)–(B5): twirl of an optimal separable comparison state

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

/-- arXiv:1707.05543v2, PDF p.28, Lemma 1 (B4)-(B5): twirling either kind
of actual optimizer preserves separability and the attained divergence. In the
constrained case it also preserves the reference marginal. Each choice has its own optimizer. -/
theorem lemma1 (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hrho : IsDensityMatrix rho) (hinv : IsPhaseInvariant rho) :
    ∀ (fixed : Bool) (sigma : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      IsComparisonOptimizer rho sigma fixed →
      IsSeparableDensity (phaseTwirl sigma) ∧
      maxRelative rho sigma = maxRelative rho (phaseTwirl sigma) ∧
      (fixed = true → traceRight (phaseTwirl sigma) = mixedIdentity (Fin 2)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P20

end
