-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_16
-- name    : SYKEdge.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:14.3162+00:00
-- url     : https://prove2.me/theorems/0094a2d8-f5fd-4aec-a8bc-25baef6f72de
-- title:
--   Lemma 4.16 — operator norm witness: $\mathbb E[\|H(g)\|_{op}\,w(g)]\ge\lambda_{\max}(\Pi_Rx\Pi_R)$ with $w=\|U\psi\|_{HS}^2$, $\mathbb Ew=1$
-- statement:
--   Let $\mathcal H$ be a $k$-uniform hypergraph, $\gamma$ Majorana operators of dimension $2^{n/2}$, $R=R_{t_0,M}$ a Krylov space (Definition 4.11, $M\ge1$) and $L=t_0+M$. There is a unit vector $\psi\in R$ with $\langle\psi,x\psi\rangle_{\mathcal F}=\lambda_{\max}(\Pi_Rx\Pi_R)$, and for every such $\psi$ the matrix-valued polynomial $F=U\psi$ has degree at most $L$ and, with $w(g)=\|F(g)\|_{HS}^2$ and $g\sim N(0,\mathrm{Id}_m)$,
--   $$\mathbb E_g\,w(g)=1,\qquad \mathbb E_g\big[\|H(g)\|_{op}\,w(g)\big]\ge\lambda_{\max}(\Pi_Rx\Pi_R),\qquad \mathbb E_g\big[\lambda_{\max}(H(g))\,w(g)\big]\ge\lambda_{\max}(\Pi_Rx\Pi_R).$$
--
--   The witness $w$ is a probability density tilting the Gaussian disorder towards Hamiltonians with a large top eigenvalue; Lemma 4.18 removes the tilt.
--
--   **Formalization Note** "$F$ has degree $\le L$" is stated as: $F$ agrees with a matrix-valued polynomial whose coefficients vanish above total degree $L$.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - generalization: E[·w(g)] ⩾ λ_max(Π_R x Π_R) stated for ‖H‖_op → E[·w(g)] ⩾ λ_max(Π_R x Π_R) stated for ‖H‖_op and, as a second conjunct, for λ_max(H); reason: Remark 1.2(1) and footnote 4 (pp.2–3) assert that the argument applies to λ_max; dropping the conjunct gives the printed statement
--   - reading: (2) "we can choose F = Uψ, where ψ ∈ R is a unit vector for which ⟨ψ, xψ⟩ = λ_max(Π_R x Π_R)" → a maximizing unit ψ ∈ R exists, and every maximizing unit ψ gives a witness F = Uψ; reason: the proof works for any such ψ; the stronger of the two readings is stated
--   - encoding: R any space of the kind of Definition 4.11 → R = R_{t₀,M} with M ⩾ 1, and L := t₀ + M; reason: for M = 0, R = {0} has no unit vector and λ_max(Π_R x Π_R) is undefined; L is not defined in the lemma, and t₀ + M is the L of Lemma 4.12
--   - encoding: F ∈ K(ℝ^ℋ, ℂ^{N×N}) of degree ⩽ L, F = Uψ → Uψ as a function of g, together with a coefficient family P of degree ⩽ L with P(g) = (Uψ)(g) for every g; reason: U is recorded as a function of g; a matrix-valued polynomial is determined by its coefficient family and its values
--   - encoding: ⟨ψ, xψ⟩_F = λ_max(Π_R x Π_R) → re⟨ψ, xψ⟩_F = λ_max(Π_R x Π_R); reason: x is Hermitian (p.23), so ⟨ψ, xψ⟩ is real
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.16, p.31; footnote 4, p.3

import Mathlib
import Definitions.Def_SYKEdge_Hermite
import Definitions.Def_SYKEdge_Krylov
open Matrix MeasureTheory

namespace SYKEdge

/-- **Lemma 4.16** (Operator Norm Witness), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.31; the `λ_max` form from footnote 4, p.3.

Let `R = R_{t₀,M}` be a space of the kind of Definition 4.11 and `L = t₀ + M`. Then there is
`F ∈ K(ℝ^H, ℂ^{N×N})` of degree `⩽ L` with `E_{g∼N(0,Id_m)}[‖H(g)‖_op·w(g)] ⩾ λ_max(Π_R x Π_R)`, where
(1) `w(g) := ‖F(g)‖²_HS`, (2) one can choose `F = Uψ` with `ψ ∈ R` a unit vector with
`⟨ψ, xψ⟩_F = λ_max(Π_R x Π_R)`, and (3) `E_g w(g) = 1`. By footnote 4 the same holds with `‖H(g)‖_op`
replaced by `λ_max(H(g))`.

**Formalization Note.** A maximizing unit `ψ ∈ R` exists, and every such `ψ` gives a witness `F = Uψ`:
`F` agrees with a matrix-valued polynomial of degree `⩽ L`, `E w = 1`, and both
`E[‖H(g)‖_op w(g)]` and `E[λ_max(H(g)) w(g)]` are `⩾ λ_max(Π_R x Π_R)`. `R_{t₀,M}` has `M ⩾ 1`
(for `M = 0`, `R = 0`). `⟨ψ, xψ⟩` is real (`x` is Hermitian); its real part is compared. -/
theorem lemma_4_16 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S)
    (t₀ M : ℕ) (hM : 1 ≤ M)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 2 ^ (n / 2))
    (γ : Fin n → Matrix ι ι ℂ) (hγ : IsMajoranaFamily γ) :
    (∃ ψ : Fock m, ψ ∈ krylovR S t₀ M ∧ normF ψ = 1 ∧
      (fockInner ψ (xop S ψ)).re = lamMaxOn S (krylovR S t₀ M)) ∧
    ∀ ψ : Fock m, ψ ∈ krylovR S t₀ M → normF ψ = 1 →
      (fockInner ψ (xop S ψ)).re = lamMaxOn S (krylovR S t₀ M) →
      (∃ P : MatPoly m ι, P.DegLE (t₀ + M) ∧ ∀ g, P.eval g = Umap γ S ψ g) ∧
      ∫ g, hsNorm (Umap γ S ψ g) ^ 2 ∂stdGauss (Fin m) = 1 ∧
      lamMaxOn S (krylovR S t₀ M) ≤
        ∫ g, opNorm (syk γ S g) * hsNorm (Umap γ S ψ g) ^ 2 ∂stdGauss (Fin m) ∧
      lamMaxOn S (krylovR S t₀ M) ≤
        ∫ g, lamMax (syk γ S g) * hsNorm (Umap γ S ψ g) ^ 2 ∂stdGauss (Fin m) := by sorry

end SYKEdge
