-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_15
-- name    : SYKEdge.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:04.934195+00:00
-- url     : https://prove2.me/theorems/ce9867ec-7c08-4efa-8f91-0efeee402615
-- title:
--   Lemma 4.15 — intertwining $MU=Ux$
-- statement:
--   With $\mathcal H$, $\gamma$ and $U$ as in Proposition 4.14, let $(MF)(g)=H(g)F(g)$ be left multiplication by the SYK Hamiltonian $H(g)=m^{-1/2}\sum_ig_i\Gamma_{S_i}$. Then
--   $$MU=Ux$$
--   as linear maps from $\mathcal F$ to matrix-valued polynomials: for every $\psi\in\mathcal F$ and every $g\in\mathbb R^m$, $H(g)\,(U\psi)(g)=(U(x\psi))(g)$.
--
--   The twisted boson $x$ is thus the Hamiltonian seen through the embedding $U$.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - encoding: MU = Ux as linear maps F → K(ℝ^ℋ, ℂ^{N×N}) → for every ψ, the functions g ↦ H(g)(Uψ)(g) and g ↦ (U(xψ))(g) are equal; reason: a matrix-valued polynomial is determined by its values
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.15, p.30

import Mathlib
import Definitions.Def_SYKEdge_Hermite

namespace SYKEdge

/-- **Lemma 4.15** (Intertwining), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.30.

`MU = Ux` as linear maps `F → K(ℝ^H, ℂ^{N×N})`, where `(MF)(g) := H(g)F(g)`.

**Formalization Note.** Stated pointwise: for every `ψ ∈ F`, `M(Uψ)` and `U(xψ)` are the same function of
`g ∈ ℝ^m`. The hypergraph satisfies the §3 standing assumptions and the Majorana family has dimension
`2^{n/2}`. -/
theorem lemma_4_15 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 2 ^ (n / 2))
    (γ : Fin n → Matrix ι ι ℂ) (hγ : IsMajoranaFamily γ) (ψ : Fock m) :
    Mmap γ S (Umap γ S ψ) = Umap γ S (xop S ψ) := by sorry

end SYKEdge
