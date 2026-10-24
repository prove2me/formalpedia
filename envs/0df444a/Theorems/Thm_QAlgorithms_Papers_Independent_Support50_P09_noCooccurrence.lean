-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_noCooccurrence
-- name    : QAlgorithms.Papers.Independent.Support50.P09.noCooccurrence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:56:17.275462+00:00
-- url     : https://prove2.me/theorems/7815cfbd-eb68-46ea-9227-937875004e45
-- title:
--   Lemma III.6 (No co-occurrence)
-- statement:
--   Let $m\ge1$ and let $|\phi\rangle^{A_1\cdots A_mR}$ be a normalized pure state on finite nonzero Hilbert spaces. All entropies are von Neumann entropies in bits of marginals of this same state. For $K\subseteq[m]$, write $A_K=\bigotimes_{i\in K}A_i$ and
--   $$
--   C_\phi(K)=\frac12\left(\sum_{i\in K}H(A_i)+H(R)-H(A_KR)\right).
--   $$
--   Let $\mathcal R_\phi$ be the closure of achievable nonnegative rate tuples: for every $\epsilon>0$, every sufficiently large positive blocklength admits independent local CPTP encoders and a joint receiver CPTP decoder, with $\log_2\dim C_i\le nQ_i$ and squared fidelity at least $1-\epsilon$ with the entire original pure state on $A^nR^n$. The reference is untouched; no auxiliary communication or supplied shared entanglement is allowed.
--
--   Let $L_1,\ldots,L_m\subseteq[m]$. Suppose the real linear system $\sum_{k\in L_i}Q_k=C_\phi(L_i)$ for $i=1,\ldots,m$ has exactly one solution, including existence. Then
--   $$
--   \nexists j\ne k\quad\forall i\in[m],\quad(j\in L_i\ \Longleftrightarrow\ k\in L_i).
--   $$
--   No feasibility condition on that solution is required.
--
--   This is the incidence-column obstruction used in the vertex analysis. The source’s word “pair” is read as two distinct elements, following its proof.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 11, Lemma III.6 (No co-occurrence)

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

/-- Lemma III.6, PDF p.11: "pair" means DISTINCT elements, as its
column-dependence proof requires. Unique solvability includes existence. -/
theorem noCooccurrence (hm : 0 < m) (L : Fin m → Finset (Fin m))
    (hunique : ∃! Q : Fin m → ℝ,
      ∀ j, (∑ i ∈ L j, Q i) = entropyThreshold (pureDensity phi) (L j)) :
    ¬ ∃ j k : Fin m, j ≠ k ∧ ∀ i, (j ∈ L i ↔ k ∈ L i) := by sorry

end Compression

end QAlgorithms.Papers.Independent.Support50.P09

end
