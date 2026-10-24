-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_distributedCompression_inner
-- name    : QAlgorithms.Papers.Independent.Support50.P09.distributedCompression_inner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:50:01.564017+00:00
-- url     : https://prove2.me/theorems/53ed26e7-fe00-4d35-a632-acd15c8cc1e5
-- title:
--   Theorem II.1: multiparty distributed compression inner bound (seed paper result)
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   Every real tuple $Q$ satisfying all subset inequalities belongs to the closed operational region:
--   $$
--   \left[\forall K\subseteq[m],\quad \sum_{i\in K}Q_i\ge C_\phi(K)\right]\ \Longrightarrow\ Q\in\mathcal R_\phi.
--   $$
--
--   This is the sufficient rate region obtained by multiparty distributed compression. Boundary membership follows the source’s closure convention.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 5, Theorem II.1: multiparty distributed compression inner bound (seed paper result)

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

/-- Theorem II.1, PDF p.5: sufficient rates belong to the CLOSED region
(Definition II.1 and the limiting proof, pp.3,8–9). -/
theorem distributedCompression_inner (hm : 0 < m) :
    entropyPolyhedron (pureDensity phi) ⊆ multipartyCompressionRegion (pureDensity phi) := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
