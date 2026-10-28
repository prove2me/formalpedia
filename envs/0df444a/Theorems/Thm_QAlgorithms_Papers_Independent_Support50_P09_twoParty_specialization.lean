-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_twoParty_specialization
-- name    : QAlgorithms.Papers.Independent.Support50.P09.twoParty_specialization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:52:25.461581+00:00
-- url     : https://prove2.me/theorems/fb4acff9-4333-4875-bbec-74d89a885f50
-- title:
--   Unnumbered specialization of (5) and (6) to two parties
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   Specialize to $m=2$. For every $Q\in\mathbb R^2$, the inner family of subset inequalities is equivalent to
--   $$
--   Q_1\ge\tfrac12 I(A_1;R),\qquad Q_2\ge\tfrac12 I(A_2;R),\qquad
--   Q_1+Q_2\ge\tfrac12[H(A_1)+H(A_2)+H(A_1A_2)].
--   $$
--   The outer family is equivalent to these same two singleton inequalities together with
--   $$
--   Q_1+Q_2\ge\tfrac12[H(A_1)+H(A_2)+H(A_1A_2)]-E_{\rm sq}(\phi^{A_1A_2}),
--   $$
--   where $E_{\rm sq}$ is half the infimum of conditional mutual information over all finite extensions.
--
--   This records both exact two-party reductions without asserting a new FQSW theorem.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 7, Unnumbered specialization of (5) and (6) to two parties

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered two-party specialization, PDF p.7: EXACT reductions of both
(5) and (6), including the singleton mutual-information inequalities. -/
theorem twoParty_specialization {D : Fin 2 → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {R : Type} [Fintype R] [Nonempty R]
    (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1) (Q : Fin 2 → ℝ) :
    let rho := pureDensity phi
    let a := forgetEnvironment rho
    let H1 := entropyAt (trivialExtension a) {0}
    let H2 := entropyAt (trivialExtension a) {1}
    let I1 := H1 + vnEntropy (traceLeft rho) - entropyAt rho {0}
    let I2 := H2 + vnEntropy (traceLeft rho) - entropyAt rho {1}
    (Q ∈ entropyPolyhedron rho ↔ I1/2 ≤ Q 0 ∧ I2/2 ≤ Q 1 ∧
      (H1 + H2 + vnEntropy a)/2 ≤ Q 0 + Q 1) ∧
    (Q ∈ outerPolyhedron rho ↔ I1/2 ≤ Q 0 ∧ I2/2 ≤ Q 1 ∧
      (H1 + H2 + vnEntropy a)/2 - halfExtensionSquashed .total a ≤ Q 0 + Q 1) := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
