-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_squashed_product_subadditive
-- name    : QAlgorithms.Papers.Independent.Support50.P09.squashed_product_subadditive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:04:26.494669+00:00
-- url     : https://prove2.me/theorems/e8770019-7880-44ca-96b4-d69a26401e39
-- title:
--   Proposition V.3: subadditivity on tensor-product states
-- statement:
--   For a normalized state $\rho^{X_1\cdots X_m}$ with $m\ge1$ finite nonzero local systems, define
--   $$
--   E_{\rm sq}(\rho)=\frac12\inf_{\widetilde\rho:\operatorname{Tr}_E\widetilde\rho=\rho}
--   \left[\sum_{i=1}^m H(X_i\mid E)_{\widetilde\rho}-H(X_1\cdots X_m\mid E)_{\widetilde\rho}\right].
--   $$
--   Entropies are in bits. The infimum ranges over all normalized extensions and every positive finite dimension of $E$, with no dimension bound or attainment assumption. One-party inputs use this same entropy expression and have value zero.
--
--   Let $\rho$ be a state on $X_1\cdots X_m$ and $\sigma$ a state on $Y_1\cdots Y_m$, allowing different positive local dimensions. Construct their independent product and group the output parties as $X_iY_i$. Then
--   $$
--   E_{\rm sq}(X_1Y_1;\ldots;X_mY_m)_{\rho\otimes\sigma}
--   \le E_{\rm sq}(X_1;\ldots;X_m)_\rho+E_{\rm sq}(Y_1;\ldots;Y_m)_\sigma.
--   $$
--
--   This states the source’s subadditivity, without strengthening it to later additivity results.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 18, Proposition V.3: subadditivity on tensor-product states

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition V.3, PDF p.18, (55): subadditivity on the ACTUAL independent
partywise product, allowing different local dimensions in the two inputs. -/
theorem squashed_product_subadditive {m : ℕ} (hm : 0 < m) {D F : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (sigma : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    halfExtensionSquashed .total (partyProduct rho sigma) ≤
      halfExtensionSquashed .total rho + halfExtensionSquashed .total sigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
