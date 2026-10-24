-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_distributedCompression_outer
-- name    : QAlgorithms.Papers.Independent.Support50.P09.distributedCompression_outer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:50:45.611981+00:00
-- url     : https://prove2.me/theorems/14870452-bccd-4418-946d-b15610ac0d69
-- title:
--   Theorem II.2: squashed-entanglement outer bound
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
--   Every tuple in the closed operational rate region satisfies
--   $$
--   \forall K\subseteq[m],\qquad \sum_{i\in K}Q_i\ge C_\phi(K)-E_{\rm sq}(\phi^{A_K}).
--   $$
--   The correction is evaluated on the actual $A_K$ marginal and lies outside the factor $1/2$ in $C_\phi$. For $K=\varnothing$ its value is defined to be zero.
--
--   This is the necessary rate bound, extended to the closure by continuity of the linear inequalities.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 6, Theorem II.2: squashed-entanglement outer bound

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

/-- Theorem II.2, PDF p.6: the unrestricted-extension correction lies outside 1/2.
The necessary inequalities extend to the closed rate region. -/
theorem distributedCompression_outer (hm : 0 < m) :
    multipartyCompressionRegion (pureDensity phi) ⊆ outerPolyhedron (pureDensity phi) := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
