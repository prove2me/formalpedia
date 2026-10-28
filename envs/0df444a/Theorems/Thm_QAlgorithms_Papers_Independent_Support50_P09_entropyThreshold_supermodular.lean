-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_entropyThreshold_supermodular
-- name    : QAlgorithms.Papers.Independent.Support50.P09.entropyThreshold_supermodular
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:54:35.867527+00:00
-- url     : https://prove2.me/theorems/d8f1aab9-f940-461a-9a80-aadccbe6c755
-- title:
--   Lemma III.4 (Superadditivity): entropy set-function supermodularity
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   For any subsets $K,L\subseteq[m]$,
--   $$
--   C_\phi(K\cup L)+C_\phi(K\cap L)\ge C_\phi(K)+C_\phi(L).
--   $$
--   Overlapping, disjoint and empty subsets are included.
--
--   This is supermodularity of the entropy set function, called “Superadditivity” in the source.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 10, Lemma III.4 (Superadditivity): entropy set-function supermodularity

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

/-- Lemma III.4 (source name: Superadditivity), PDF p.10, (18):
supermodularity for overlapping, disjoint and empty subsets of the SAME source. -/
theorem entropyThreshold_supermodular (hm : 0 < m) (K L : Finset (Fin m)) :
    entropyThreshold (pureDensity phi) K + entropyThreshold (pureDensity phi) L ≤
      entropyThreshold (pureDensity phi) (K ∪ L) +
      entropyThreshold (pureDensity phi) (K ∩ L) := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
