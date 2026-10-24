-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_squashed_continuous
-- name    : QAlgorithms.Papers.Independent.Support50.P09.squashed_continuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:05:09.312989+00:00
-- url     : https://prove2.me/theorems/c4eec47c-7a38-461a-8c90-1255c31c0d29
-- title:
--   Proposition V.5: continuity of multipartite squashed entanglement
-- statement:
--   For a normalized state $\rho^{X_1\cdots X_m}$ with $m\ge1$ finite nonzero local systems, define
--   $$
--   E_{\rm sq}(\rho)=\frac12\inf_{\widetilde\rho:\operatorname{Tr}_E\widetilde\rho=\rho}
--   \left[\sum_{i=1}^m H(X_i\mid E)_{\widetilde\rho}-H(X_1\cdots X_m\mid E)_{\widetilde\rho}\right].
--   $$
--   Entropies are in bits. The infimum ranges over all normalized extensions and every positive finite dimension of $E$, with no dimension bound or attainment assumption. One-party inputs use this same entropy expression and have value zero.
--
--   On each fixed honest-party space the function $E_{\rm sq}$ is continuous. More explicitly, let $d_i=\dim X_i$ and
--   $$
--   \omega(\epsilon)=16\sqrt\epsilon\log_2\left(\prod_i d_i\right)+2(m+1)h_2(2\sqrt\epsilon),
--   $$
--   where $h_2(p)=-p\log_2p-(1-p)\log_2(1-p)$ and $0\log_20=0$. For all density operators $\rho,\sigma$ on that space, if $\epsilon\ge0$, $2\sqrt\epsilon\le1$ and the full trace norm satisfies $\|\rho-\sigma\|_1\le\epsilon$, then
--   $$
--   |E_{\rm sq}(\rho)-E_{\rm sq}(\sigma)|\le\omega(\epsilon),\qquad
--   \lim_{\epsilon\downarrow0}\omega(\epsilon)=0.
--   $$
--
--   This preserves the printed equation (67), with no extension-dimension dependence. The small-error restriction applies to the explicit modulus; qualitative continuity has no proximity restriction.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 18, Proposition V.5: continuity of multipartite squashed entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition V.5, PDF pp.18–19: continuity on every fixed honest-party
space, plus the PRINTED (67) modulus on 2 sqrt(eps)<=1. Full trace norm is
used, unlike Lemma V.4's local half-trace convention. No cap on E is imposed. -/
theorem squashed_continuous {m : ℕ} (hm : 0 < m) {D : Fin m → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] :
    Continuous (fun rho : {rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ //
      IsDensityMatrix rho} => halfExtensionSquashed .total rho.val) ∧
    (∀ (rho sigma : Matrix (RegisterBasis D) (RegisterBasis D) ℂ),
      IsDensityMatrix rho → IsDensityMatrix sigma → ∀ eps : ℝ,
      0 ≤ eps → 2 * Real.sqrt eps ≤ 1 → traceNorm (rho-sigma) ≤ eps →
      |halfExtensionSquashed .total rho - halfExtensionSquashed .total sigma| ≤
        continuityModulus D eps) ∧
    Filter.Tendsto (continuityModulus D) (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
