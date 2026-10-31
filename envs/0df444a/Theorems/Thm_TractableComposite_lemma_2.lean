-- Prove2me | Theorems.Thm_TractableComposite_lemma_2
-- name    : TractableComposite.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:43.897512+00:00
-- url     : https://prove2.me/theorems/1842a856-e17c-471d-94a2-85459ec5bb7b
-- title:
--   Lemma 2 — the envelope over a product of chain simplices is the staircase interpolant
-- statement:
--   Let $R=\prod_iR_i\subseteq\mathbb R^{d\times(n+1)}$, where $R_i$ is a simplex with vertices $\bar\upsilon_{i0}\le\bar\upsilon_{i1}\le\dots\le\bar\upsilon_{in}$ (a chain) and $\bar\upsilon_{ij0}=a_{i0}$ for all $j$. Let $\psi:R\to\mathbb R$ be concave-extendable from $\operatorname{vert}(R)$ and supermodular on the lattice $\operatorname{vert}(R)$. Then every $r\in R$ lies in some staircase simplex, and for every movement vector $\pi$ and every convex combination $r=\sum_kw_k\operatorname{ext}(R,\Pi(\pi,k))$,
--
--   $$\operatorname{conc}_R(\psi)(r)=\sum_{k=0}^{dn}w_k\,\psi(\operatorname{ext}(R,\Pi(\pi,k))).$$
--
--   That is, $\operatorname{conc}_R(\psi)=\psi^{\mathcal S}$. Applied to $R=Q$ it gives Proposition 4.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - encoding: concave envelope conc_D(g), and conc_D(g|_X) → concOn: supremum over finite convex combinations of points of D (resp. X); reason: the concave envelope of a function on a convex set; same values at every point of the domain when the function is bounded above on it (the unbounded case is the generalization entry below)
--   - reading: conc(η)(z) = η^𝒮(z) for every z, with 𝒮 the staircase triangulation → (a) every point lies in some staircase simplex; (b) for every staircase π and every convex combination z = ∑ wₖ V(π,k), conc(z) = ∑ wₖ η(V(π,k)); reason: η^𝒮 is the affine interpolant on the simplex of 𝒮 containing z; (a) and (b) together are exactly this
--   - encoding: vert(·) of a product of simplices → the explicit grid of listed vertices (prodVert); reason: the vertices of a product of simplices are the products of their vertices
--   - reading: conc_R(ψ)(r) = ψ^𝒮(r) for every r ∈ ℝ; supermodular over the lattice defined over R → every r ∈ R; supermodular on vert(R); reason: the printed ℝ is ill-typed (conc_R(ψ) lives on R); the proof and Proposition 4 use supermodularity on vert(R)
--   - encoding: R_i is a simplex with vertices ῡ_i0,…,ῡ_in forming a chain, ῡ_ij0 = a_i0 → AffineIndependent ℝ (υ i), Monotone (υ i), υ i j 0 = υ i 0 0; reason: same conditions; the constant a_i0 is not otherwise used
--   - generalization: ψ a real function on R, concave-extendable from vert(R), hence bounded above on R → ψ a total function on the ambient space (values off R are not read), with ConcaveExtendable read through concOn, whose sSup is 0 on an unbounded set, so some unbounded ψ also meet the hypothesis; reason: every ψ of the source is an instance and concOn is then its envelope; for an extra ψ the hypothesis turns the left side into the envelope over the vertices, so the conclusion is the same vertex identity
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Lemma 2, p.10

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_TractableComposite_prodSimplex
import Definitions.Def_TractableComposite_prodVert
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_TractableComposite_ConcaveExtendable
import Definitions.Def_TractableComposite_IsMovement
import Definitions.Def_TractableComposite_stairVtx
import Definitions.Def_TractableComposite_stairSimplex

namespace TractableComposite

/-- **Lemma 2**, p.10. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Lemma 2, p.10.

Let `R = ∏ᵢ Rᵢ ⊆ ℝ^{d×(n+1)}`, where `Rᵢ` is a simplex in `ℝ^{n+1}` whose vertices `ῡᵢ₀, …, ῡᵢₙ` form a
chain `ῡᵢ₀ ≤ ⋯ ≤ ῡᵢₙ` with `ῡᵢⱼ₀ = aᵢ₀` for all `j`. If `ψ : R → ℝ` is concave-extendable from vert(R) and
supermodular over the lattice vert(R), then `conc_R(ψ)(r) = ψ^𝒮(r)` for every `r ∈ R`, where `𝒮` is the
staircase triangulation of `R`.

**Formalization Note.** Reading R6: the printed "for every r ∈ ℝ" means `r ∈ R`, and "supermodular over
the lattice defined over R" means over vert(R). "Rᵢ is a simplex with vertices ῡᵢⱼ" is
`AffineIndependent ℝ (υ i)`; the chain is `Monotone (υ i)` (coordinatewise order); `ῡᵢⱼ₀ = aᵢ₀` is
`υ i j 0 = υ i 0 0` (the constant `aᵢ₀` is not otherwise used). Reading R8 for `ψ^𝒮`, as in
`proposition_3`. -/
theorem lemma_2 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (υ : Fin d → Fin (n + 1) → (Fin (n + 1) → ℝ))
    (hυ_simplex : ∀ i, AffineIndependent ℝ (υ i)) (hυ_chain : ∀ i, Monotone (υ i))
    (hυ_first : ∀ i j, υ i j 0 = υ i 0 0) (ψ : (Fin d → Fin (n + 1) → ℝ) → ℝ)
    (hψ_ext : ConcaveExtendable (prodSimplex υ) (prodVert υ) ψ)
    (hψ_sup : Supermodularity.Monotonicity.SupermodularOn ψ (prodVert υ)) :
    (∀ r ∈ prodSimplex υ, ∃ π : Fin (d * n) → Fin d, IsMovement π ∧ r ∈ stairSimplex υ π) ∧
    ∀ π : Fin (d * n) → Fin d, IsMovement π →
    ∀ w : Fin (d * n + 1) → ℝ, (∀ k, 0 ≤ w k) → ∑ k, w k = 1 →
      concOn (prodSimplex υ) ψ (∑ k, w k • stairVtx υ π k) = ∑ k, w k * ψ (stairVtx υ π k) := by sorry

end TractableComposite
