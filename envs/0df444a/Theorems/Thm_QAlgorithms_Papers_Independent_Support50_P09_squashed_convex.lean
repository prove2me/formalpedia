-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_squashed_convex
-- name    : QAlgorithms.Papers.Independent.Support50.P09.squashed_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:03:41.407145+00:00
-- url     : https://prove2.me/theorems/90380a58-c738-4662-94d3-a303281a7e4e
-- title:
--   Unnumbered main property (54): convexity of E_sq
-- statement:
--   For a normalized state $\rho^{X_1\cdots X_m}$ with $m\ge1$ finite nonzero local systems, define
--   $$
--   E_{\rm sq}(\rho)=\frac12\inf_{\widetilde\rho:\operatorname{Tr}_E\widetilde\rho=\rho}
--   \left[\sum_{i=1}^m H(X_i\mid E)_{\widetilde\rho}-H(X_1\cdots X_m\mid E)_{\widetilde\rho}\right].
--   $$
--   Entropies are in bits. The infimum ranges over all normalized extensions and every positive finite dimension of $E$, with no dimension bound or attainment assumption. One-party inputs use this same entropy expression and have value zero.
--
--   Let $\rho,\sigma$ be normalized density operators on the same honest-party systems, let $0\le\lambda\le1$, and set $\tau=\lambda\rho+(1-\lambda)\sigma$. Then
--   $$
--   E_{\rm sq}(\tau)\le\lambda E_{\rm sq}(\rho)+(1-\lambda)E_{\rm sq}(\sigma).
--   $$
--
--   This is convexity for the actual computed mixture, including both endpoints.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 17, Unnumbered main property (54): convexity of E_sq

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered convexity property, PDF p.17, (54): actual mixture and endpoints. -/
theorem squashed_convex {m : ℕ} (hm : 0 < m) {D : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho sigma : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    halfExtensionSquashed .total (stateMixture lambda rho sigma) ≤
      lambda * halfExtensionSquashed .total rho +
      (1-lambda) * halfExtensionSquashed .total sigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
