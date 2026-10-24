-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_tightSets_unionIntersection
-- name    : QAlgorithms.Papers.Independent.Support50.P09.tightSets_unionIntersection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:55:21.246533+00:00
-- url     : https://prove2.me/theorems/0cd367ed-5d77-4765-a2a4-69ebd74def74
-- title:
--   Corollary III.5: tight sets closed under union and intersection
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   Define $P_H=\{Q\in\mathbb R^m:\sum_{i\in K}Q_i\ge C_\phi(K)\text{ for every }K\subseteq[m]\}$. For a permutation $\pi$, let $S_{\pi,l}$ be its last $l$ participants and define the corner $q^\pi$ by $q^\pi_{\pi(j)}=\tfrac12 I(A_{\pi(j)};A_{\pi(j+1)}\cdots A_{\pi(m)}R)$. Write $\mathcal Q=\{q^\pi:\pi\in S_m\}$; different permutations may give the same point.
--
--   Let $Q\in P_H$ and let $K,L\subseteq[m]$ satisfy $\sum_{i\in K}Q_i=C_\phi(K)$ and $\sum_{i\in L}Q_i=C_\phi(L)$. Then both conclusions hold:
--   $$
--   \sum_{i\in K\cup L}Q_i=C_\phi(K\cup L),\qquad
--   \sum_{i\in K\cap L}Q_i=C_\phi(K\cap L).
--   $$
--
--   Feasibility makes the collection of tight subsets closed under union and intersection.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 10, Corollary III.5: tight sets closed under union and intersection

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

/-- Corollary III.5, PDF p.10: feasibility is retained; both tightness equations
for the union and intersection are conclusions. -/
theorem tightSets_unionIntersection (hm : 0 < m) (Q : Fin m → ℝ)
    (hQ : Q ∈ entropyPolyhedron (pureDensity phi)) (K L : Finset (Fin m))
    (hK : (∑ i ∈ K, Q i) = entropyThreshold (pureDensity phi) K)
    (hL : (∑ i ∈ L, Q i) = entropyThreshold (pureDensity phi) L) :
    (∑ i ∈ K ∪ L, Q i) = entropyThreshold (pureDensity phi) (K ∪ L) ∧
    (∑ i ∈ K ∩ L, Q i) = entropyThreshold (pureDensity phi) (K ∩ L) := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
