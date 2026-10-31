-- Prove2me | Theorems.Thm_TractableComposite_proposition_3
-- name    : TractableComposite.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:57.443987+00:00
-- url     : https://prove2.me/theorems/20256da3-9ba6-495c-b4dd-2eac037ce26e
-- title:
--   Proposition 3 — the envelope over $\Delta$ is the staircase interpolant
-- statement:
--   Let $\Delta_i=\{z_i\in\mathbb R^{n+1}\mid0\le z_{in}\le\dots\le z_{i1}\le z_{i0}=1\}$ and $\Delta=\prod_i\Delta_i$. Then:
--
--   1. $\operatorname{vert}(\Delta)$ is a lattice (closed under componentwise $\vee$ and $\wedge$);
--   2. every $z\in\Delta$ lies in some staircase simplex $\Xi_\pi$;
--   3. if $\eta:\Delta\to\mathbb R$ is supermodular on $\operatorname{vert}(\Delta)$ and concave-extendable from $\operatorname{vert}(\Delta)$, then for every movement vector $\pi$ and every convex combination $z=\sum_kw_k\operatorname{ext}(\Delta,\Pi(\pi,k))$,
--
--   $$\operatorname{conc}_\Delta(\eta)(z)=\sum_{k=0}^{dn}w_k\,\eta(\operatorname{ext}(\Delta,\Pi(\pi,k))).$$
--
--   That is, $\operatorname{conc}_\Delta(\eta)=\eta^{\mathcal S}$, the interpolant on the staircase triangulation. It is the base case that Lemma 2 transports to any product of chain simplices.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - encoding: concave envelope conc_D(g), and conc_D(g|_X) → concOn: supremum over finite convex combinations of points of D (resp. X); reason: the concave envelope of a function on a convex set; same values at every point of the domain when the function is bounded above on it (the unbounded case is the generalization entry below)
--   - reading: conc(η)(z) = η^𝒮(z) for every z, with 𝒮 the staircase triangulation → (a) every point lies in some staircase simplex; (b) for every staircase π and every convex combination z = ∑ wₖ V(π,k), conc(z) = ∑ wₖ η(V(π,k)); reason: η^𝒮 is the affine interpolant on the simplex of 𝒮 containing z; (a) and (b) together are exactly this
--   - encoding: vert(Δ) → the explicit vertex grid of the ζ_j = (1,…,1,0,…,0); reason: Appendix A: vert(Δ_i) = {ζ_ij}
--   - encoding: vert(Δ) defines a lattice → closure of the vertex grid under componentwise ⊔ and ⊓; reason: a subset of the componentwise lattice is a lattice in the induced order iff it is closed under these operations
--   - generalization: η a real function on Δ, concave-extendable from vert(Δ), hence bounded above on Δ → η a total function on the ambient space (values off Δ are not read), with ConcaveExtendable read through concOn, whose sSup is 0 on an unbounded set, so some unbounded η also meet the hypothesis; reason: every η of the source is an instance and concOn is then its envelope; for an extra η the hypothesis turns the left side into the envelope over the vertices, so the conclusion is the same vertex identity
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Proposition 3, p.8 (proof, Appendix A, p.35)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_TractableComposite_prodVert
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_TractableComposite_ConcaveExtendable
import Definitions.Def_TractableComposite_IsMovement
import Definitions.Def_TractableComposite_stairVtx
import Definitions.Def_TractableComposite_stairSimplex
import Definitions.Def_TractableComposite_zeta
import Definitions.Def_TractableComposite_Delta

namespace TractableComposite

/-- **Proposition 3**, p.8. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Proposition 3, p.8 (proof: Appendix A, p.35).

Let `Δᵢ = {zᵢ ∈ ℝ^{n+1} | 0 ≤ zᵢₙ ≤ ⋯ ≤ zᵢ₁ ≤ zᵢ₀ = 1}` and `Δ = ∏ᵢ Δᵢ`. Then vert(Δ) is a lattice. If
`η : Δ → ℝ` is supermodular on vert(Δ) and concave-extendable from vert(Δ), then
`conc_Δ(η)(z) = η^𝒮(z)` for every `z ∈ Δ`, where `𝒮` is the staircase triangulation of `Δ`.

**Formalization Note.** vert(Δ) is `{(ζ_{1j₁}, …, ζ_{dj_d})}` with `ζⱼ = (1,…,1,0,…,0)` (ones in coordinates
`0..j`; Appendix A); "defines a lattice" is closure under the componentwise `⊔`, `⊓`. Reading R8:
`η^𝒮` is the piecewise-affine interpolant of `η` on the staircase triangulation, stated as two clauses:
every `z ∈ Δ` lies in some staircase simplex `Ξ_π`, and for every movement vector `π` and every convex
combination `z = ∑ₖ wₖ ext(Δ, Π(π,k))`, `conc_Δ(η)(z) = ∑ₖ wₖ η(ext(Δ, Π(π,k)))`. -/
theorem proposition_3 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (∀ x ∈ (prodVert (fun _ : Fin d => zeta n)), ∀ y ∈ (prodVert (fun _ : Fin d => zeta n)), x ⊔ y ∈ (prodVert (fun _ : Fin d => zeta n)) ∧ x ⊓ y ∈ (prodVert (fun _ : Fin d => zeta n))) ∧
    (∀ z ∈ Delta d n, ∃ π : Fin (d * n) → Fin d, IsMovement π ∧ z ∈ stairSimplex (fun _ => zeta n) π) ∧
    ∀ η : (Fin d → Fin (n + 1) → ℝ) → ℝ, Supermodularity.Monotonicity.SupermodularOn η (prodVert (fun _ : Fin d => zeta n)) →
      ConcaveExtendable (Delta d n) (prodVert (fun _ : Fin d => zeta n)) η →
      ∀ π : Fin (d * n) → Fin d, IsMovement π →
      ∀ w : Fin (d * n + 1) → ℝ, (∀ k, 0 ≤ w k) → ∑ k, w k = 1 →
        concOn (Delta d n) η (∑ k, w k • stairVtx (fun _ => zeta n) π k) =
          ∑ k, w k * η (stairVtx (fun _ => zeta n) π k) := by sorry

end TractableComposite
