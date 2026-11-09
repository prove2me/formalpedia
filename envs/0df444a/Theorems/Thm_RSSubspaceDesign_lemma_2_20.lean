-- Prove2me | Theorems.Thm_RSSubspaceDesign_lemma_2_20
-- name    : RSSubspaceDesign.lemma_2_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:26.408414+00:00
-- url     : https://prove2.me/theorems/7cf1fee3-1613-4373-9cd0-ee692ba333c6
-- title:
--   Lemma 2.20 (i)–(ii) — a downward-closed set of independent conjugates (existence; computation is lemma\_2\_20\_computation)
-- statement:
--   Let $K\subseteq F$ be finite fields, let $\sigma_1,\dots,\sigma_g$ generate $G=\mathrm{Gal}(F/K)$, and let $u_1,\dots,u_d\in F[X]$ be linearly independent over $K(X)$, where $g,d\ge1$. For $\omega\in\mathbb Z_{\ge0}^g$ write $\sigma^\omega=\sigma_1^{\omega_1}\cdots\sigma_g^{\omega_g}$. Then there is a set $B\subseteq\mathbb Z_{\ge0}^g$ of size $d$, downward closed under the coordinatewise order, such that
--
--   1. the polynomial $P(X)=\det\big(\sigma^\omega(u_a)(X)\big)_{\omega\in B,\,1\le a\le d}$ is nonzero;
--   2. for any distinct points $\alpha_1,\dots,\alpha_n\in F$,
--   $$\sum_{i=1}^n|\{\omega\in B:\sigma^\omega(\alpha_i)\ne\alpha_i\}|\;\le\;d\log_2 d\cdot\max_{\sigma\in\{\sigma_1,\dots,\sigma_g\}}|\{\alpha_i:\sigma(\alpha_i)\ne\alpha_i\}|.\qquad(2.2)$$
--
--   Here $\sigma\in G$ acts on $F[X]$ through the coefficients and fixes $X$. Proposition 4.3 uses $P$ as a Galois (Moore-type) determinant whose vanishing at the points is controlled by (2.2).
--
--   This item is the existence part, (i)–(ii). The lemma's last sentence, that such a $B$ can be computed deterministically in polynomial time, is the companion item `RSSubspaceDesign.lemma_2_20_computation`.
--
--   Differences from the source:
--   - encoding: ω ∈ ℤ^g_{≥0} with the coordinatewise order; σ^ω; σ acting on F[X] → Fin g → ℕ with the pointwise order; the ordered product σ₀^{ω₀} ⋯ σ_{g−1}^{ω_{g−1}}; Polynomial.map of σ; reason: Lean convention; same objects (0-based indices)
--   - encoding: det(σ^ω(u_a))_{ω∈B, 1≤a≤d} ≠ 0 → the determinant with rows indexed through an enumeration Fin d ≃ B is nonzero for every enumeration; reason: reordering rows changes only the sign
--   - encoding: linearly independent over K(X) → LinearIndependent over RatFunc K of the images in RatFunc F (ratFuncAlgebra); reason: the standard inclusion K(X) ⊆ F(X)
--   - encoding: max over σ ∈ {σ₁, …, σ_g} of |{αᵢ : σ(αᵢ) ≠ αᵢ}| → Finset.sup over j of the number of indices i with σⱼ(αᵢ) ≠ αᵢ; reason: the points are distinct, so points and indices are counted alike
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Lemma 2.20 (i)–(ii), pp.14–15 (PDF pp.16–17), display (2.2)

import Mathlib
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra
import Definitions.Def_RSSubspaceDesign_IsConjugateSet

open Polynomial

namespace RSSubspaceDesign

/-- **Lemma 2.20 (i)–(ii) (A downward-closed set of independent conjugates), existence part.**
Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Lemma 2.20,
pp.14–15, statements (i) and (ii) with display (2.2). The lemma's last sentence (computing `B`
in polynomial time) is the companion item `lemma_2_20_computation`.

Let `K ⊆ F` be finite fields, let `σ₁, …, σ_g` generate `G = Gal(F/K)`, and let
`u₁, …, u_d ∈ F[X]` be linearly independent over `K(X)`, where `g, d ≥ 1`. There is a set
`B ⊆ ℤ^g_{≥0}` of size `d`, downward closed under the coordinatewise order, with properties (i) and
(ii) (`IsConjugateSet`).

**Formalization Note.** `Gal(F/K)` is `F ≃ₐ[K] F`; "generate" is `Subgroup.closure (range σ) = ⊤`.
Linear independence over `K(X)` is taken in `F(X)` via `ratFuncAlgebra`. -/
theorem lemma_2_20 {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] {g d : ℕ}
    (hg : 1 ≤ g) (hd : 1 ≤ d) (σ : Fin g → (F ≃ₐ[K] F))
    (hσ : Subgroup.closure (Set.range σ) = ⊤) (u : Fin d → F[X])
    (hu : letI := ratFuncAlgebra K F
      LinearIndependent (RatFunc K) fun a => algebraMap F[X] (RatFunc F) (u a)) :
    ∃ B : Finset (Fin g → ℕ), IsConjugateSet K σ u B := by sorry

end RSSubspaceDesign
