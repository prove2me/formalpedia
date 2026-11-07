-- Prove2me | Theorems.Thm_SYKEdge_proposition_4_7
-- name    : SYKEdge.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:53.035353+00:00
-- url     : https://prove2.me/theorems/59ee86f2-d03f-42f2-ab21-f2023a90511b
-- title:
--   Proposition 4.7 — SYK moments: $\varphi(x^{2\ell})=\mathbb E\operatorname{tr}(H^{2\ell})$
-- statement:
--   Let $\mathcal H$ be a $k$-uniform hypergraph with $m$ hyperedges, $H=H(g)=m^{-1/2}\sum_ig_i\Gamma_{S_i}$ the SYK Hamiltonian with $g\sim N(0,\mathrm{Id}_m)$, on Majorana operators of dimension $2^{n/2}$, and $x=a+a^*$ the collective twisted boson. For every $\ell\ge0$,
--   $$\varphi(x^{2\ell})=\mathbb E\operatorname{tr}\big(H^{2\ell}\big).$$
--
--   This exact identity is the bridge of the upper bound: spectral bounds on $x$ bound all even trace moments of the SYK Hamiltonian.
--
--   **Formalization Note** Both sides are complex numbers; $\operatorname{tr}$ is the normalized trace.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Proposition 4.7, p.25

import Mathlib
import Definitions.Def_SYKEdge_Fock
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
open Matrix MeasureTheory

namespace SYKEdge

/-- **Proposition 4.7** (SYK Moments), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.25.

`φ(x^{2ℓ}) = E tr(H^{2ℓ})`, where `H = |H|^{−1/2} Σ_{S∈H} g_S Γ_S` is the SYK Hamiltonian (8).

**Formalization Note.** Stated for every `ℓ ∈ ℕ`, as an identity of complex numbers; `tr` is the
normalized trace, `g ∼ N(0, Id_m)`, and the representation has dimension `2^{n/2}` (p.15). -/
theorem proposition_4_7 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 2 ^ (n / 2))
    (γ : Fin n → Matrix ι ι ℂ) (hγ : IsMajoranaFamily γ) (ℓ : ℕ) :
    fockPhi (xop S ^ (2 * ℓ)) = ∫ g, ntr (syk γ S g ^ (2 * ℓ)) ∂stdGauss (Fin m) := by sorry

end SYKEdge
