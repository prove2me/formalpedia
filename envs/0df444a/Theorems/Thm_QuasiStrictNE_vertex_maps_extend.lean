-- Prove2me | Theorems.Thm_QuasiStrictNE_vertex_maps_extend
-- name    : QuasiStrictNE.vertex_maps_extend
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:10.742682+00:00
-- url     : https://prove2.me/theorems/73f3308c-eb93-49ba-9348-2405c15b47d3
-- title:
--   pp.11–12 — the vertex maps (2) extend to continuous simplicial maps $S_1,R_2,S_2,R_1$
-- statement:
--   Let $(A,B)$ be a bimatrix game with $m,n\ge 1$ and fix relative-interior points $p_F$ ($F\in\mathcal C_m$) and $q_G$ ($G\in\mathcal C_n$). The vertex maps
--   $$
--   S_1(p_F)=\ell_m(\mathrm{supp}(p_F)),\quad R_2(p_F)=\ell_n(BR_2(p_F)),\quad S_2(q_G)=\ell_n(\mathrm{supp}(q_G)),\quad R_1(q_G)=\ell_m(BR_1(q_G))
--   $$
--   extend to continuous simplicial maps
--   $$
--   S_1:\Delta_m\to\Delta_m,\qquad R_2:\Delta_m\to\Delta_n,\qquad S_2:\Delta_n\to\Delta_n,\qquad R_1:\Delta_n\to\Delta_m .
--   $$
--   Precisely: each map sends its source simplex into its target simplex, is continuous on its source simplex, and on every chain $F_0\subsetneq\cdots\subsetneq F_r$ of $\mathcal C_m$ (resp. $G_0\subsetneq\cdots\subsetneq G_s$ of $\mathcal C_n$) and barycentric weights $\lambda$,
--   $$
--   S_1\Bigl(\sum_t\lambda_t p_{F_t}\Bigr)=\sum_t\lambda_t\,\ell_m(\mathrm{supp}(p_{F_t})),
--   $$
--   and likewise for $R_2$, $S_2$, $R_1$.
--
--   Differences from the source:
--   - encoding: relint F (interior in the affine hull); a fixed point pF per face → intrinsicInterior ℝ F; the selection is a function p on sets with p F ∈ intrinsicInterior ℝ F for F in the complex; reason: Lean convention; same selections
--   - encoding: the continuous extensions S1, R2, S2, R1 (well-defined by Proposition 2) → the maps simplicialExt …, with MapsTo, ContinuousOn and the barycentric formula for every chain and every weight vector; reason: the barycentric formula for every representation is the well-definedness; same maps
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 5, pp.11–12

import Mathlib
import Definitions.Def_QuasiStrictNE_IsFaceChain
import Definitions.Def_QuasiStrictNE_S1
import Definitions.Def_QuasiStrictNE_R2
import Definitions.Def_QuasiStrictNE_S2
import Definitions.Def_QuasiStrictNE_R1

namespace QuasiStrictNE

/-- **The four vertex maps (2) extend to continuous simplicial maps** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 5,
pp.11–12: "All these maps send vertices of the simplicial complex Km (or Kn) to vertices of the
simplicial complex Um (or Un). We verify that whenever vertices span a simplex of K, their images
span a simplex of U. Then we use the same notation for their continuous extensions: S1 : ∆m → ∆m,
R2 : ∆m → ∆n, S2 : ∆n → ∆n, R1 : ∆n → ∆m", and p.12: "By Proposition 2, the four vertex maps extend to
continuous simplicial maps").

Let `(A, B)` be a bimatrix game with `m, n ≥ 1`, and let `p`, `q` select relative-interior points of
the faces of `Cm`, `Cn`. Then:

1. `S1` maps `Δm` into `Δm`, is continuous on `Δm`, and for every chain `F₀ ⊊ ⋯ ⊊ F_r` of `Cm` and all
   barycentric weights `λ`, `S1(∑ λ_t p F_t) = ∑ λ_t ℓm(supp(p F_t))`;
2. `R2` maps `Δm` into `Δn`, is continuous on `Δm`, and `R2(∑ λ_t p F_t) = ∑ λ_t ℓn(BR2(p F_t))`;
3. `S2` maps `Δn` into `Δn`, is continuous on `Δn`, and for every chain `G₀ ⊊ ⋯ ⊊ G_s` of `Cn`,
   `S2(∑ μ_u q G_u) = ∑ μ_u ℓn(supp(q G_u))`;
4. `R1` maps `Δn` into `Δm`, is continuous on `Δn`, and `R1(∑ μ_u q G_u) = ∑ μ_u ℓm(BR1(q G_u))`.

**Formalization Note** The barycentric formula is asserted for every chain and every representation,
so the maps are well defined (independent of the representation chosen by `simplicialExt`). -/
theorem vertex_maps_extend {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (A B : Matrix (Fin m) (Fin n) ℝ)
    (p : Set (Fin m → ℝ) → (Fin m → ℝ)) (q : Set (Fin n → ℝ) → (Fin n → ℝ))
    (hp : ∀ F ∈ Cm B, p F ∈ intrinsicInterior ℝ F)
    (hq : ∀ G ∈ Cn A, q G ∈ intrinsicInterior ℝ G) :
    (Set.MapsTo (S1 B p) (stdSimplex ℝ (Fin m)) (stdSimplex ℝ (Fin m)) ∧
      ContinuousOn (S1 B p) (stdSimplex ℝ (Fin m)) ∧
      ∀ (σ : Finset (Set (Fin m → ℝ))) (w : Set (Fin m → ℝ) → ℝ), IsFaceChain (Cm B) σ →
        (∀ F ∈ σ, 0 ≤ w F) → ∑ F ∈ σ, w F = 1 →
        S1 B p (∑ F ∈ σ, w F • p F) = ∑ F ∈ σ, w F • ell m (supp (p F))) ∧
    (Set.MapsTo (R2 B p) (stdSimplex ℝ (Fin m)) (stdSimplex ℝ (Fin n)) ∧
      ContinuousOn (R2 B p) (stdSimplex ℝ (Fin m)) ∧
      ∀ (σ : Finset (Set (Fin m → ℝ))) (w : Set (Fin m → ℝ) → ℝ), IsFaceChain (Cm B) σ →
        (∀ F ∈ σ, 0 ≤ w F) → ∑ F ∈ σ, w F = 1 →
        R2 B p (∑ F ∈ σ, w F • p F) = ∑ F ∈ σ, w F • ell n (BR2 B (p F))) ∧
    (Set.MapsTo (S2 A q) (stdSimplex ℝ (Fin n)) (stdSimplex ℝ (Fin n)) ∧
      ContinuousOn (S2 A q) (stdSimplex ℝ (Fin n)) ∧
      ∀ (τ : Finset (Set (Fin n → ℝ))) (w : Set (Fin n → ℝ) → ℝ), IsFaceChain (Cn A) τ →
        (∀ G ∈ τ, 0 ≤ w G) → ∑ G ∈ τ, w G = 1 →
        S2 A q (∑ G ∈ τ, w G • q G) = ∑ G ∈ τ, w G • ell n (supp (q G))) ∧
    (Set.MapsTo (R1 A q) (stdSimplex ℝ (Fin n)) (stdSimplex ℝ (Fin m)) ∧
      ContinuousOn (R1 A q) (stdSimplex ℝ (Fin n)) ∧
      ∀ (τ : Finset (Set (Fin n → ℝ))) (w : Set (Fin n → ℝ) → ℝ), IsFaceChain (Cn A) τ →
        (∀ G ∈ τ, 0 ≤ w G) → ∑ G ∈ τ, w G = 1 →
        R1 A q (∑ G ∈ τ, w G • q G) = ∑ G ∈ τ, w G • ell m (BR1 A (q G))) := by sorry

end QuasiStrictNE
