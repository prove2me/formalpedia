-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_corners_inRegion
-- name    : QAlgorithms.Papers.Independent.Support50.P09.corners_inRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:53:14.553403+00:00
-- url     : https://prove2.me/theorems/d92e409b-623e-4c80-b975-2bd0cf5f25f0
-- title:
--   Lemma III.2: corner points lie in the rate region
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   Define $P_H=\{Q\in\mathbb R^m:\sum_{i\in K}Q_i\ge C_\phi(K)\text{ for every }K\subseteq[m]\}$. For a permutation $\pi$, let $S_{\pi,l}$ be its last $l$ participants and define the corner $q^\pi$ by $q^\pi_{\pi(j)}=\tfrac12 I(A_{\pi(j)};A_{\pi(j+1)}\cdots A_{\pi(m)}R)$. Write $\mathcal Q=\{q^\pi:\pi\in S_m\}$; different permutations may give the same point.
--
--   All computed corners belong to the closed operational region:
--   $$
--   \mathcal Q\subseteq\mathcal R_\phi.
--   $$
--
--   These rates supply the vertices used for time sharing and resource wasting.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 7, Lemma III.2: corner points lie in the rate region

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

/-- Lemma III.2, PDF pp.7–8: computed suffix-based corners are in the closed region. -/
theorem corners_inRegion (hm : 0 < m) :
    compressionCorners (pureDensity phi) ⊆ multipartyCompressionRegion (pureDensity phi) := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
