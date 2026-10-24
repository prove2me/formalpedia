-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_corner_suffixCharacterization
-- name    : QAlgorithms.Papers.Independent.Support50.P09.corner_suffixCharacterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:53:59.166188+00:00
-- url     : https://prove2.me/theorems/4ed74406-69df-483a-943a-9d7bf3ba80ab
-- title:
--   Lemma III.3: suffix-sum characterization of corner points
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   Define $P_H=\{Q\in\mathbb R^m:\sum_{i\in K}Q_i\ge C_\phi(K)\text{ for every }K\subseteq[m]\}$. For a permutation $\pi$, let $S_{\pi,l}$ be its last $l$ participants and define the corner $q^\pi$ by $q^\pi_{\pi(j)}=\tfrac12 I(A_{\pi(j)};A_{\pi(j+1)}\cdots A_{\pi(m)}R)$. Write $\mathcal Q=\{q^\pi:\pi\in S_m\}$; different permutations may give the same point.
--
--   For every real rate tuple $Q$,
--   $$
--   Q\in\mathcal Q\ \Longleftrightarrow\ \exists\pi\in S_m\ \forall l\in\{1,\ldots,m\},\quad
--   \sum_{i\in S_{\pi,l}}Q_i=C_\phi(S_{\pi,l}).
--   $$
--   One permutation must witness all nonempty suffix equalities.
--
--   This characterizes a corner by a triangular family of saturated constraints.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 8, Lemma III.3: suffix-sum characterization of corner points

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

/-- Lemma III.3, PDF pp.8–9: one permutation witnesses ALL nonempty suffixes. -/
theorem corner_suffixCharacterization (hm : 0 < m) (Q : Fin m → ℝ) :
    Q ∈ compressionCorners (pureDensity phi) ↔ ∃ pi : Equiv.Perm (Fin m),
      ∀ l : ℕ, 1 ≤ l → l ≤ m →
        (∑ i ∈ senderSuffix pi l, Q i) = entropyThreshold (pureDensity phi) (senderSuffix pi l) := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
