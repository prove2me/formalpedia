-- Prove2me | Theorems.Thm_WeightedEdgeColor_lemma_profile_choice_pos
-- name    : WeightedEdgeColor.lemma_profile_choice_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T08:13:28.302676+00:00
-- url     : https://prove2.me/theorems/ecaf5e0a-5faa-410e-856b-115f6ed2a77f
-- title:
--   Choosing profiles group by group (typed edges, $\beta>0$): slack and small discrepancy
-- statement:
--   This is the step "Choosing profiles group by group" in the proof of Theorem 3.1 (local-to-global rounding). From a menu of profiles at every vertex and color, it selects one profile per vertex–color pair. Every slot then keeps spare capacity, and at every vertex the coordinated fractional options deviate from their intended totals by only $O(n^{3/4})$ in weighted absolute value.
--
--   Fix constants $C_0,C_1,\theta,r_0>0$, $0<\sigma<1$, a threshold $\beta>0$, and integers $M$ (menu size), $K_s$ (slots per profile) and $r$ (number of groups). Let $G$ be a finite simple graph with weights in $(0,1]$, with an orientation $e=(u_e,v_e)$ of every edge, and with its vertices divided into $r$ groups with no edge inside a group. Let $n$ be a real parameter with $W_G(v)\le n$, and let $\mathcal C$ be a palette with $|\mathcal C|\le C_1n$.
--
--   **Data.** At every vertex $v$ and color $c$ there is a menu of $M$ profile labels $P$, with:
--
--   1. probabilities $\lambda_{v,c}(P)\ge\theta/M$, $\sum_P\lambda_{v,c}(P)=1$;
--   2. reserved spaces $R_{v,c}(P)\in\{0\}\cup[r_0,\infty)$;
--   3. fractions $a^L_{v,c}(e;P,i)\ge0$ of edge $e$ in slot $i$ of $P$, and $a^S_{v,c}(e;P)\ge0$ in the reserved space of $P$, the latter only where $R_{v,c}(P)>0$.
--
--   Every edge is either *large* ($w_e\ge\beta$), with only slot fractions, or *small* ($w_e<\beta$), with only reserve fractions.
--
--   There are also targets $0\le y_{e,c}\le C_0/n$ such that, at each end $v$ of $e$,
--
--   $$
--   \sum_P\Big(\sum_ia^L_{v,c}(e;P,i)+a^S_{v,c}(e;P)\Big)=y_{e,c}.
--   $$
--
--   The capacities hold in expectation with slack $\sigma$:
--
--   $$
--   \sum_{e\ni v}a^L_{v,c}(e;P,i)\le(1-\sigma)\lambda_{v,c}(P),\qquad\sum_{e\ni v}w_e\,a^S_{v,c}(e;P)\le(1-\sigma)\lambda_{v,c}(P)R_{v,c}(P).
--   $$
--
--   **Conclusion.** For all sufficiently large $n$ there is a choice of labels $P_{v,c}$ with the following properties. For the paired options
--
--   $$
--   X^L(e,c,i,j)=\frac{a^L_{u_e,c}(e;P_{u_e,c},i)\,a^L_{v_e,c}(e;P_{v_e,c},j)}{y_{e,c}\,\lambda_{u_e,c}(P_{u_e,c})\,\lambda_{v_e,c}(P_{v_e,c})},\qquad
--   X^S(e,c)=\frac{a^S_{u_e,c}(e;P_{u_e,c})\,a^S_{v_e,c}(e;P_{v_e,c})}{y_{e,c}\,\lambda_{u_e,c}(P_{u_e,c})\,\lambda_{v_e,c}(P_{v_e,c})}
--   $$
--
--   (zero when $y_{e,c}=0$), the following hold.
--
--   1. Every slot of a chosen profile has total fraction at most $1-\sigma/2$.
--   2. Every chosen reserved space has weighted load $\sum_{e\ni v}w_eX^S(e,c)\le(1-\sigma/2)R_{v,c}(P_{v,c})$.
--   3. Every vertex satisfies
--
--   $$
--   \sum_{e\ni v}w_e\,\big|S_e-\mu_e\big|=O\big(n^{3/4}\big),\qquad S_e=\sum_c\Big(\sum_{i,j}X^L(e,c,i,j)+X^S(e,c)\Big),\quad\mu_e=\sum_cy_{e,c}.
--   $$
--
--   The threshold and the implied constant depend only on the fixed constants. In the source these are the capacity bound "$\le(1-\sigma/2)h(P,i)$" and the discrepancy bound $Z_v\le Q^{(r)}_v=O(n^{3/4})$, with the factor $\rho$ of the source absorbed into the fractions $a$ and the targets $y$.
--
--   **Formalization Note.** Labels are `Fin M` and slots `Fin Ks`. The fractions are indexed by the vertex at which they live, $a^L(v,c,e,P,i)$, and only the ends of $e$ are used. The options are passed as functions $XL$, $XS$ equal to the displayed quotients, where Lean's $x/0=0$ matches the source's convention for $y_{e,c}=0$.
-- source:
--   R. Gajjala, A. Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, arXiv:2611.03190 (preprint of November 2, 2026), proof of Theorem 3.1, 'Choosing profiles group by group', pp.37-40, (C.5)-(C.10) and the load bound on p.40; uses Proposition A.4

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph

set_option autoImplicit false
namespace WeightedEdgeColor

theorem lemma_profile_choice_pos (C₀ C₁ θ σ r₀ β : ℝ) (M Ks r : ℕ)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hθ : 0 < θ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hr₀ : 0 < r₀)
    (hβ : 0 < β) :
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ g : V → Fin r,
      (∀ (e : E) (u v : V), G.ends e = s(u, v) → g u ≠ g v) →
      ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ (y : E → 𝒞 → ℝ) (lam : V → 𝒞 → Fin M → ℝ) (R : V → 𝒞 → Fin M → ℝ)
        (aL : V → 𝒞 → E → Fin M → Fin Ks → ℝ) (aS : V → 𝒞 → E → Fin M → ℝ),
      (∀ e c, 0 ≤ y e c ∧ y e c ≤ C₀ / n) →
      (∀ v c P, θ / M ≤ lam v c P) → (∀ v c, ∑ P, lam v c P = 1) →
      (∀ v c P, R v c P = 0 ∨ r₀ ≤ R v c P) →
      (∀ v c e P i, 0 ≤ aL v c e P i) → (∀ v c e P, 0 ≤ aS v c e P) →
      (∀ v c e P, aS v c e P ≠ 0 → 0 < R v c P) →
      -- every edge is either large (slot fractions only) or small (reserve fractions only)
      (∀ v c e P i, aL v c e P i ≠ 0 → β ≤ G.w e) → (∀ v c e P, aS v c e P ≠ 0 → G.w e < β) →
      -- the fractions of `e` at each of its ends add up to `y e c`
      (∀ v c e, v ∈ G.ends e → ∑ P, (∑ i, aL v c e P i + aS v c e P) = y e c) →
      -- capacities hold in expectation, with slack `σ`
      (∀ v c P i, ∑ e ∈ G.inc v, aL v c e P i ≤ (1 - σ) * lam v c P) →
      (∀ v c P, ∑ e ∈ G.inc v, G.w e * aS v c e P ≤ (1 - σ) * lam v c P * R v c P) →
      ∃ Pc : V → 𝒞 → Fin M, ∀ (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ) (XS : E → 𝒞 → ℝ),
        (∀ e c i j, XL e c i j = aL (src e) c e (Pc (src e) c) i * aL (tgt e) c e (Pc (tgt e) c) j /
            (y e c * lam (src e) c (Pc (src e) c) * lam (tgt e) c (Pc (tgt e) c))) →
        (∀ e c, XS e c = aS (src e) c e (Pc (src e) c) * aS (tgt e) c e (Pc (tgt e) c) /
            (y e c * lam (src e) c (Pc (src e) c) * lam (tgt e) c (Pc (tgt e) c))) →
        -- every slot of a chosen profile keeps slack `σ / 2`
        (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
           + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ / 2) ∧
        (∀ v c, ∑ e ∈ G.inc v, G.w e * XS e c ≤ (1 - σ / 2) * R v c (Pc v c)) ∧
        -- small weighted discrepancy at every vertex
        ∀ v, ∑ e ∈ G.inc v, G.w e *
          |∑ c, (∑ i, ∑ j, XL e c i j + XS e c) - ∑ c, y e c| ≤ K * n ^ (3 / 4 : ℝ) := by sorry

end WeightedEdgeColor
