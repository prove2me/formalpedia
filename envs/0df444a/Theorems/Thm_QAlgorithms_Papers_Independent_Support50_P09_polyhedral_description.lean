-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_polyhedral_description
-- name    : QAlgorithms.Papers.Independent.Support50.P09.polyhedral_description
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:57:38.555854+00:00
-- url     : https://prove2.me/theorems/242eb1bc-7a52-4e94-a234-628ee7373083
-- title:
--   Unnumbered main geometric result: P_H=P_V, vertices and recession cone
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   Define $P_H=\{Q\in\mathbb R^m:\sum_{i\in K}Q_i\ge C_\phi(K)\text{ for every }K\subseteq[m]\}$. For a permutation $\pi$, let $S_{\pi,l}$ be its last $l$ participants and define the corner $q^\pi$ by $q^\pi_{\pi(j)}=\tfrac12 I(A_{\pi(j)};A_{\pi(j+1)}\cdots A_{\pi(m)}R)$. Write $\mathcal Q=\{q^\pi:\pi\in S_m\}$; different permutations may give the same point.
--
--   Let $P_V=\operatorname{conv}(\mathcal Q)+\mathbb R_{\ge0}^m$. Define $\operatorname{rec}(P_H)=\{v:\forall x\in P_H,\forall t\ge0,\ x+tv\in P_H\}$. Then
--   $$
--   P_H=P_V,\qquad \operatorname{ext}(P_H)=\mathcal Q,\qquad
--   \operatorname{rec}(P_H)=\mathbb R_{\ge0}^m.
--   $$
--   The recession cone is retained, as in equations (14), (15) and Step 3; the prose on page 11 that omits it is corrected.
--
--   This is the paper’s geometric description of its sufficient rate region; it makes no distinctness or irredundancy claim.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 13, Unnumbered main geometric result: P_H=P_V, vertices and recession cone

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

/-- Unnumbered geometric result, PDF pp.9,11–13, (14),(15),(32):
P_H=P_V, its vertices are precisely the corners, and its recession cone is
nonnegative. Correction: p.11's prose omits the cone; pp.9,13 include it. -/
theorem polyhedral_description (hm : 0 < m) :
    entropyPolyhedron (pureDensity phi) = vertexPolyhedron (pureDensity phi) ∧
    (entropyPolyhedron (pureDensity phi)).extremePoints ℝ = compressionCorners (pureDensity phi) ∧
    rateRecession (entropyPolyhedron (pureDensity phi)) = positiveCone m := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
