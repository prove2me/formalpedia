-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_fullySeparable_squashed_zero
-- name    : QAlgorithms.Papers.Independent.Support50.P09.fullySeparable_squashed_zero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:02:19.003802+00:00
-- url     : https://prove2.me/theorems/a5996ef9-fe08-4621-a3a6-d0f8500c7270
-- title:
--   Unnumbered example: fully separable states have zero squashed entanglement
-- statement:
--   For a normalized state $\rho^{X_1\cdots X_m}$ with $m\ge1$ finite nonzero local systems, define
--   $$
--   E_{\rm sq}(\rho)=\frac12\inf_{\widetilde\rho:\operatorname{Tr}_E\widetilde\rho=\rho}
--   \left[\sum_{i=1}^m H(X_i\mid E)_{\widetilde\rho}-H(X_1\cdots X_m\mid E)_{\widetilde\rho}\right].
--   $$
--   Entropies are in bits. The infimum ranges over all normalized extensions and every positive finite dimension of $E$, with no dimension bound or attainment assumption. One-party inputs use this same entropy expression and have value zero.
--
--   Suppose $\rho$ is fully separable across all $m$ parties, meaning it admits a finite convex decomposition into local product density matrices. Then
--   $$
--   E_{\rm sq}(\rho)=0.
--   $$
--   In finite dimensions this is equivalent to the source’s pure-product decomposition by local spectral refinement.
--
--   The classical-record extension is part of the construction; it is not an additional hypothesis, and no converse is claimed.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 16, Unnumbered example: fully separable states have zero squashed entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered separable example, PDF p.16, (43): full sender separability
implies zero half-normalized squashed entanglement. No converse is asserted. -/
theorem fullySeparable_squashed_zero {m : ℕ} (hm : 0 < m) (s : FiniteState m)
    (hsep : IsMixedFullySeparable s) : halfExtensionSquashed .total s.rho = 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
