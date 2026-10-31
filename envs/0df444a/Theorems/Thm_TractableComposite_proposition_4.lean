-- Prove2me | Theorems.Thm_TractableComposite_proposition_4
-- name    : TractableComposite.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:44.0403+00:00
-- url     : https://prove2.me/theorems/30846917-566f-4ee5-b34e-d662a09583fe
-- title:
--   Proposition 4 — $\operatorname{conc}_Q(\bar\phi)$ is the staircase interpolant of $\bar\phi$
-- statement:
--   Let $\phi:\mathbb R^d\to\mathbb R$ be continuous and $\bar\phi(s)=\phi(s_{1n},\dots,s_{dn})$. Assume $\bar\phi$ is concave-extendable from $\operatorname{vert}(Q)$ and supermodular on the lattice $\operatorname{vert}(Q)$. Then every $s\in Q$ lies in some staircase simplex $\Upsilon_\pi$, and for every movement vector $\pi$ and every convex combination $s=\sum_kw_k\mathcal V(\pi,k)$,
--
--   $$\operatorname{conc}_Q(\bar\phi)(s)=\sum_{k=0}^{dn}w_k\,\bar\phi(\mathcal V(\pi,k)).$$
--
--   That is, $\operatorname{conc}_Q(\bar\phi)=\bar\phi^{\mathcal S}$ on $Q$, where $\mathcal S$ is the staircase triangulation of $Q$. This is what makes the interpolating inequality (15) facet-defining.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - encoding: concave envelope conc_D(g), and conc_D(g|_X) → concOn: supremum over finite convex combinations of points of D (resp. X); reason: the concave envelope of a function on a convex set; same values at every point of the domain
--   - reading: conc(η)(z) = η^𝒮(z) for every z, with 𝒮 the staircase triangulation → (a) every point lies in some staircase simplex; (b) for every staircase π and every convex combination z = ∑ wₖ V(π,k), conc(z) = ∑ wₖ η(V(π,k)); reason: η^𝒮 is the affine interpolant on the simplex of 𝒮 containing z; (a) and (b) together are exactly this
--   - encoding: vert(·) of a product of simplices → the explicit grid of listed vertices (prodVert); reason: the vertices of a product of simplices are the products of their vertices
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Proposition 4, p.10

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_TractableComposite_phiBar
import Definitions.Def_TractableComposite_vtx
import Definitions.Def_TractableComposite_Q
import Definitions.Def_TractableComposite_vertQ
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_TractableComposite_ConcaveExtendable
import Definitions.Def_TractableComposite_IsMovement
import Definitions.Def_TractableComposite_stairVtx
import Definitions.Def_TractableComposite_stairSimplex

namespace TractableComposite

/-- **Proposition 4**, p.10. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Proposition 4, p.10.

Let `φ : ℝ^d → ℝ` be an outer-function and `φ̄(s) = φ(s₁ₙ, …, s_dn)`. If `φ̄` is concave-extendable from
vert(Q) and supermodular on the lattice vert(Q), then `conc_Q(φ̄)(s) = φ̄^𝒮(s)` for each `s ∈ Q`, where `𝒮`
is the staircase triangulation of `Q`.

**Formalization Note.** Standing data: `d, n ≥ 1`, rows of `a` strictly increasing (R9), `φ` continuous
(p.3). Reading R8 for `φ̄^𝒮`: every `s ∈ Q` lies in some `Υ_π`, and for every movement vector `π` and every
convex combination `s = ∑ₖ wₖ 𝒱(π,k)`, `conc_Q(φ̄)(s) = ∑ₖ wₖ φ̄(𝒱(π,k))`. -/
theorem proposition_4 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (a : Fin d → Fin (n + 1) → ℝ) (ha : ∀ i, StrictMono (a i)) (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ)
    (hext : ConcaveExtendable (Q a) (vertQ a) (phiBar φ))
    (hsup : Supermodularity.Monotonicity.SupermodularOn (phiBar φ) (vertQ a)) :
    (∀ s ∈ Q a, ∃ π : Fin (d * n) → Fin d, IsMovement π ∧ s ∈ stairSimplex (vtx a) π) ∧
    ∀ π : Fin (d * n) → Fin d, IsMovement π →
    ∀ w : Fin (d * n + 1) → ℝ, (∀ k, 0 ≤ w k) → ∑ k, w k = 1 →
      concOn (Q a) (phiBar φ) (∑ k, w k • stairVtx (vtx a) π k) =
        ∑ k, w k * phiBar φ (stairVtx (vtx a) π k) := by sorry

end TractableComposite
