-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_6
-- name    : SYKEdge.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:44.104854+00:00
-- url     : https://prove2.me/theorems/8bca62f6-3e70-4dbb-8ed8-55dc9c187e7e
-- title:
--   Lemma 4.6 — twisted bosonic mapping $\varphi(x_{S_1}\cdots x_{S_{2\ell}})=\mathbb E[g_{S_1}\cdots g_{S_{2\ell}}]\cdot\operatorname{tr}[\Gamma_{S_1}\cdots\Gamma_{S_{2\ell}}]$
-- statement:
--   Let $\mathcal H=(S_1,\dots,S_m)$ be a $k$-uniform hypergraph, $\gamma_1,\dots,\gamma_n$ Majorana operators of dimension $2^{n/2}$, and $g\sim N(0,\mathrm{Id}_m)$. For every $\ell\ge0$ and every sequence of hyperedges $S_{i_1},\dots,S_{i_{2\ell}}$ of $\mathcal H$,
--   $$\varphi\big(x_{S_{i_1}}x_{S_{i_2}}\cdots x_{S_{i_{2\ell}}}\big)=\mathbb E\big[g_{i_1}g_{i_2}\cdots g_{i_{2\ell}}\big]\cdot\operatorname{tr}\big[\Gamma_{S_{i_1}}\Gamma_{S_{i_2}}\cdots\Gamma_{S_{i_{2\ell}}}\big],$$
--   where $\varphi(T)=\langle f_0,Tf_0\rangle$ and $\operatorname{tr}$ is the normalized trace.
--
--   The vacuum moments of the deterministic operators $x_S$ thus reproduce the Gaussian-averaged moments of Majorana monomials, signs included.
--
--   **Formalization Note** The sequence is a map $\{1,\dots,2\ell\}\to\{1,\dots,m\}$ of hyperedge indices; repetitions are allowed. Products are ordered from left to right.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.6, p.23

import Mathlib
import Definitions.Def_SYKEdge_Fock
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
open Matrix MeasureTheory

namespace SYKEdge

/-- **Lemma 4.6** (Twisted Bosonic Mapping), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.23.

For any `S₁, …, S_{2ℓ} ∈ H`,
`φ(x_{S₁} ⋯ x_{S_{2ℓ}}) = E[g_{S₁} g_{S₂} ⋯ g_{S_{2ℓ}}] · tr[Γ_{S₁} Γ_{S₂} ⋯ Γ_{S_{2ℓ}}]`.

**Formalization Note.** The sequence `S₁, …, S_{2ℓ}` is a map `i : Fin (2ℓ) → Fin m` into the
hyperedge indices (repetitions allowed); `g ∼ N(0, Id_m)` with one variable per index (footnote 6).
Products are ordered left to right. `tr` is the normalized trace and the representation has dimension
`2^{n/2}` (p.15). -/
theorem lemma_4_6 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 2 ^ (n / 2))
    (γ : Fin n → Matrix ι ι ℂ) (hγ : IsMajoranaFamily γ) (ℓ : ℕ) (i : Fin (2 * ℓ) → Fin m) :
    fockPhi ((List.ofFn fun j => (xS S (i j) : Module.End ℂ (Fock m))).prod) =
      (((∫ g, ∏ j, g (i j) ∂stdGauss (Fin m) : ℝ)) : ℂ) *
        ntr (List.ofFn fun j => monomial γ (S (i j))).prod := by sorry

end SYKEdge
