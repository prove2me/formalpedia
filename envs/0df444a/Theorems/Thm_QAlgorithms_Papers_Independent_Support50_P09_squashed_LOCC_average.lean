-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_squashed_LOCC_average
-- name    : QAlgorithms.Papers.Independent.Support50.P09.squashed_LOCC_average
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:02:58.466076+00:00
-- url     : https://prove2.me/theorems/7d429644-cb9f-46ad-b27a-6ce2637c9b72
-- title:
--   Proposition V.2: average monotonicity under LOCC
-- statement:
--   For a normalized state $\rho^{X_1\cdots X_m}$ with $m\ge1$ finite nonzero local systems, define
--   $$
--   E_{\rm sq}(\rho)=\frac12\inf_{\widetilde\rho:\operatorname{Tr}_E\widetilde\rho=\rho}
--   \left[\sum_{i=1}^m H(X_i\mid E)_{\widetilde\rho}-H(X_1\cdots X_m\mid E)_{\widetilde\rho}\right].
--   $$
--   Entropies are in bits. The infimum ranges over all normalized extensions and every positive finite dimension of $E$, with no dimension bound or attainment assumption. One-party inputs use this same entropy expression and have value zero.
--
--   Let a finite adaptive LOCC protocol applied to $\rho$ have terminal normalized states $\rho_j$ and probabilities $p_j$. Local dimensions may change with the branch, and classical transcripts may be forgotten. Then
--   $$
--   \sum_jp_jE_{\rm sq}(\rho_j)\le E_{\rm sq}(\rho).
--   $$
--   Zero-probability branches use arbitrary normalized states with the subnormalized equation $p_j\rho_j=\mathcal E_j(\rho)$, without dividing by $p_j$.
--
--   This retains the proposition’s average monotonicity, including selective and deterministic finite-round operations.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 16, Proposition V.2: average monotonicity under LOCC

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition V.2, PDF pp.16–17: AVERAGE monotonicity for finite adaptive
LOCC, including branch-dependent dimensions and forgotten transcripts.
Zero-probability outcomes use subnormalized equations, not division by zero. -/
theorem squashed_LOCC_average {m : ℕ} (hm : 0 < m) :
    IsAdaptiveLOCCMonotone (fun s : FiniteState m => halfExtensionSquashed .total s.rho) := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
