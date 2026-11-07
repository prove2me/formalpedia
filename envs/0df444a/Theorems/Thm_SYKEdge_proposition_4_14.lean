-- Prove2me | Theorems.Thm_SYKEdge_proposition_4_14
-- name    : SYKEdge.proposition_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:58.176203+00:00
-- url     : https://prove2.me/theorems/3ea4b6dd-3b64-4d48-816b-a981ed1e4a28
-- title:
--   Proposition 4.14 — isometric embedding $\langle\psi,\psi'\rangle_{\mathcal F}=\langle U\psi,U\psi'\rangle_{\mathcal K}$
-- statement:
--   Let $\mathcal H=(S_1,\dots,S_m)$ be a $k$-uniform hypergraph, $\gamma$ Majorana operators of dimension $2^{n/2}$, and $U$ the linear map $(Uf_r)(g)=h_r(g)\Gamma^r$ from the Fock space to matrix-valued polynomials, where $h_r$ are the normalized multivariate Hermite polynomials and $\Gamma^r=\Gamma_{S_1}^{r_1}\cdots\Gamma_{S_m}^{r_m}$. For all $\psi,\psi'\in\mathcal F$,
--   $$\langle\psi,\psi'\rangle_{\mathcal F}=\langle U\psi,U\psi'\rangle_{\mathcal K}=\mathbb E_{g\sim N(0,\mathrm{Id}_m)}\operatorname{tr}\big((U\psi)(g)^*(U\psi')(g)\big).$$
--
--   This is a twisted Wiener–Itô chaos isometry.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Proposition 4.14, p.30

import Mathlib
import Definitions.Def_SYKEdge_Hermite

namespace SYKEdge

/-- **Proposition 4.14** (Isometric Embedding), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.30.

For any `ψ, ψ' ∈ F`, `⟨ψ, ψ'⟩_F = ⟨Uψ, Uψ'⟩_K`, where `(U f_r)(g) := h_r(g)Γ^r` (26) and
`⟨F, G⟩_K = E_{g∼N(0,Id_m)} tr(F(g)*G(g))`.

**Formalization Note.** The hypergraph satisfies the §3 standing assumptions and the Majorana family has
dimension `2^{n/2}` (p.15). -/
theorem proposition_4_14 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 2 ^ (n / 2))
    (γ : Fin n → Matrix ι ι ℂ) (hγ : IsMajoranaFamily γ) (ψ ψ' : Fock m) :
    fockInner ψ ψ' = Kinner (Umap γ S ψ) (Umap γ S ψ') := by sorry

end SYKEdge
