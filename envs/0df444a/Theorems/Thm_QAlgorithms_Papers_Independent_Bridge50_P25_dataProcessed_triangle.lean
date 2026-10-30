-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_dataProcessed_triangle
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.dataProcessed_triangle
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:03:36.960578+00:00
-- url     : https://prove2.me/theorems/7fef7426-bacd-4668-9400-5e445dc8783c
-- title:
--   Theorem III.1: data-processed triangle inequality
-- statement:
--   Let $P:M_{d_A}\to M_{d_B}$ be a complex-linear positive trace-preserving map between positive finite-dimensional matrix algebras. Let $\rho,\sigma'$ be input density matrices and $\sigma$ an output density matrix. For every finite real $\alpha\ge1$,
--
--   $$D_\alpha(P(\rho)\|\sigma)\le D_\alpha(\rho\|\sigma')+D_{\max}(P(\sigma')\|\sigma).$$
--
--   Here $D_\alpha$ is the sandwiched divergence in bits, $D_1$ is Umegaki relative entropy, and support failures have value $+\infty$. No full-rank or complete-positivity assumption is imposed.
--
--   This controls divergence after a positive map by an input divergence and a max-relative comparison term.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 9, Theorem III.1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Theorem III.1, PDF pp.9--10: positive trace-preserving LINEAR maps;
complete positivity and full rank are not required. Alpha=1 is included. -/
theorem dataProcessed_triangle (P : Mat I →ₗ[ℂ] Mat J)
    (positive : ∀ X : Mat I, X.PosSemidef → (P X).PosSemidef)
    (trace_preserving : ∀ X : Mat I, (P X).trace = X.trace)
    (alpha : ℝ) (halpha : 1 ≤ alpha) (rho comparison : Mat I) (sigma : Mat J)
    (hrho : IsDensityMatrix rho) (hcomparison : IsDensityMatrix comparison)
    (hsigma : IsDensityMatrix sigma) :
    paperSandwichedRenyi alpha (P rho) sigma ≤ paperSandwichedRenyi alpha rho comparison + maxRelative (P comparison) sigma := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
