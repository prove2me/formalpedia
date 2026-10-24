-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_vertex_maximalChain
-- name    : QAlgorithms.Papers.Independent.Support50.P09.vertex_maximalChain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:57:02.683458+00:00
-- url     : https://prove2.me/theorems/488d4e39-576e-4f62-a539-cd01d71800e8
-- title:
--   Proposition III.7 (Existence of a maximal chain)
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   Define $P_H=\{Q\in\mathbb R^m:\sum_{i\in K}Q_i\ge C_\phi(K)\text{ for every }K\subseteq[m]\}$. For a permutation $\pi$, let $S_{\pi,l}$ be its last $l$ participants and define the corner $q^\pi$ by $q^\pi_{\pi(j)}=\tfrac12 I(A_{\pi(j)};A_{\pi(j+1)}\cdots A_{\pi(m)}R)$. Write $\mathcal Q=\{q^\pi:\pi\in S_m\}$; different permutations may give the same point.
--
--   For every vertex $Q$ of $P_H$, there is a chain
--   $$
--   \varnothing=K_0\subsetneq K_1\subsetneq\cdots\subsetneq K_m=[m]
--   $$
--   such that the entire solution set of its $m$ nonempty-set equations is exactly the vertex:
--   $$
--   \left\{x\in\mathbb R^m:\ \sum_{k\in K_i}x_k=C_\phi(K_i),\ i=1,\ldots,m\right\}=\{Q\}.
--   $$
--   Vertices are extreme points of the feasible convex set.
--
--   The chain equations replace any defining independent system while preserving its singleton solution set.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 12, Proposition III.7 (Existence of a maximal chain)

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

/-- Proposition III.7, PDF p.12: a feasible vertex has m chain equations
whose ENTIRE solution set is the original singleton, not extra constraints. -/
theorem vertex_maximalChain (hm : 0 < m) (Q : Fin m → ℝ)
    (hvertex : Q ∈ (entropyPolyhedron (pureDensity phi)).extremePoints ℝ) :
    ∃ K : Fin (m+1) → Finset (Fin m), IsMaximalChain K ∧
      {x | chainEquations (pureDensity phi) K x} = {Q} := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
