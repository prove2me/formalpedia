-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_zeroSquashed_optimal
-- name    : QAlgorithms.Papers.Independent.Support50.P09.zeroSquashed_optimal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:51:33.082066+00:00
-- url     : https://prove2.me/theorems/d2624b96-dcde-4f45-b510-149ca861e9ed
-- title:
--   Unnumbered main consequence: optimality for zero-squashed sources
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   For a normalized state $\rho^{X_1\cdots X_m}$ with $m\ge1$ finite nonzero local systems, define
--   $$
--   E_{\rm sq}(\rho)=\frac12\inf_{\widetilde\rho:\operatorname{Tr}_E\widetilde\rho=\rho}
--   \left[\sum_{i=1}^m H(X_i\mid E)_{\widetilde\rho}-H(X_1\cdots X_m\mid E)_{\widetilde\rho}\right].
--   $$
--   Entropies are in bits. The infimum ranges over all normalized extensions and every positive finite dimension of $E$, with no dimension bound or attainment assumption. One-party inputs use this same entropy expression and have value zero.
--
--   Let $P_{\rm out}=\{Q:\sum_{i\in K}Q_i\ge C_\phi(K)-E_{\rm sq}(\phi^{A_K})\text{ for every }K\subseteq[m]\}$ and $P_H=\{Q:\sum_{i\in K}Q_i\ge C_\phi(K)\text{ for every }K\subseteq[m]\}$. Then
--   $$
--   E_{\rm sq}(\phi^{A_1\cdots A_m})=0\quad\Longrightarrow\quad
--   \mathcal R_\phi=P_H\quad\text{and}\quad P_{\rm out}=P_H.
--   $$
--   No separate zero-measure hypothesis is imposed on the subsets.
--
--   This identifies the optimal distributed-compression region for zero-squashed sources.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 6, Unnumbered main consequence: optimality for zero-squashed sources

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

section Compression

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)] [hD : ∀ i, Nonempty (D i)]

variable {R : Type} [Fintype R] [hR : Nonempty R]

variable (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1)

include hphi hD hR

/-- Unnumbered optimality consequence, PDF pp.6,24 (also p.1): zero of the
FULL sender measure suffices; zero of every subset is not assumed. -/
theorem zeroSquashed_optimal (hm : 0 < m)
    (hzero : halfExtensionSquashed .total (forgetEnvironment (pureDensity phi)) = 0) :
    multipartyCompressionRegion (pureDensity phi) = entropyPolyhedron (pureDensity phi) ∧
    outerPolyhedron (pureDensity phi) = entropyPolyhedron (pureDensity phi) := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
