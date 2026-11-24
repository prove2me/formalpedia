-- Prove2me | Theorems.Thm_WeightedEdgeColor_lemma_large_edge_rounding
-- name    : WeightedEdgeColor.lemma_large_edge_rounding
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T06:07:36.073966+00:00
-- url     : https://prove2.me/theorems/09755e6f-7a55-498f-8241-e843c40e7fa4
-- title:
--   Rounding the large edges: disjoint whole options with few unchosen edges
-- statement:
--   This is the step "Rounding the large edges" in the proof of Theorem 3.1 (local-to-global rounding). Fractional options of the large edges, which have spare capacity in every slot, are turned into a choice of whole options that never uses a slot twice. The weight left unchosen at each vertex is essentially the weight not covered by the fractional options.
--
--   Fix constants $C_1>0$, $0<\sigma<1$, $\beta>0$, $C_m>0$, $\varepsilon>0$ and an integer $K_s\ge0$. Let $G$ be a finite simple graph with weights $w:E\to(0,1]$ and an orientation $e=(u_e,v_e)$ of every edge. Let $n$ be a real parameter with $W_G(v)\le n$ for every vertex, and let $\mathcal C$ be a palette with $|\mathcal C|\le C_1n$. Every vertex–color pair $(v,c)$ has slots of sizes $b_{v,c,1},\dots,b_{v,c,K_s}$. A large option $X(e,c,i,j)\ge0$ is a fraction of edge $e$ that would receive color $c$, use slot $i$ at $(u_e,c)$ and use slot $j$ at $(v_e,c)$. Suppose that:
--
--   1. $X(e,c,i,j)>0$ only if $w_e\ge\beta$, $w_e\le b_{u_e,c,i}$ and $w_e\le b_{v_e,c,j}$;
--   2. $s_e=\sum_{c,i,j}X(e,c,i,j)\le1$ for every edge, and $\sum_{i,j}X(e,c,i,j)\le C_m/n$ for every edge and color;
--   3. every slot has total fraction at most $1-\sigma$, summed over the edges at either end that use it.
--
--   Then, for all sufficiently large $n$, every edge $e$ can be given either no option or one option $(c,i,j)$ with $X(e,c,i,j)>0$, such that no slot is used by two edges and, at every vertex $v$,
--
--   $$
--   \sum_{\substack{e\ni v,\ w_e\ge\beta\\ e\text{ unchosen}}} w_e\;\le\;\sum_{e\ni v,\ w_e\ge\beta}w_e\,(1-s_e)\;+\;\varepsilon n\;+\;O\big(n^{2/3}\big).
--   $$
--
--   The threshold and the implied constant depend only on the fixed constants, not on the number of vertices.
--
--   A chosen option colors $e$ with $c$ and places it in a slot that can hold it at each end. Since no slot is used twice, the large edges of one color at a vertex fit into that vertex's profile.
--
--   **Formalization Note.** The choice is a map $\psi:E\to$ `Option` $(\mathcal C\times$ `Fin Ks` $\times$ `Fin Ks`$)$. Edge $e$ *uses slot* $i$ at $(v,c)$ if $\psi(e)=(c,i,j)$ with $u_e=v$, or $\psi(e)=(c,j,i)$ with $v_e=v$. The source's bound $\frac{1+\xi}{1-\gamma}\sum w_er_e+O(n^{2/3})$ (C.13), with $\xi,\gamma$ arbitrarily small and $\sum_{e\ni v}w_er_e\le n$, is stated here as $\sum w_e(1-s_e)+\varepsilon n+O(n^{2/3})$.
-- source:
--   R. Gajjala, A. Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, arXiv:2611.03190 (preprint of November 2, 2026), proof of Theorem 3.1, paragraph 'Rounding the large edges', pp.40-42, claim (C.12) and bound (C.13); uses Proposition A.5

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph

set_option autoImplicit false
namespace WeightedEdgeColor

theorem lemma_large_edge_rounding (C₁ σ β Cm ε : ℝ) (Ks : ℕ)
    (hC₁ : 0 < C₁) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hβ0 : 0 < β) (hCm : 0 < Cm) (hε : 0 < ε) :
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ (b : V → 𝒞 → Fin Ks → ℝ) (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ),
      (∀ e c i j, 0 ≤ XL e c i j) →
      (∀ e c i j, XL e c i j ≠ 0 → β ≤ G.w e ∧ G.w e ≤ b (src e) c i ∧ G.w e ≤ b (tgt e) c j) →
      (∀ e, ∑ c, ∑ i, ∑ j, XL e c i j ≤ 1) →
      (∀ e c, ∑ i, ∑ j, XL e c i j ≤ Cm / n) →
      (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
         + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ) →
      ∃ ψ : E → Option (𝒞 × Fin Ks × Fin Ks),
        -- only options of positive fraction are chosen
        (∀ e c i j, ψ e = some (c, i, j) → 0 < XL e c i j) ∧
        -- no slot is used twice
        (∀ (e e' : E) (v : V) (c : 𝒞) (i : Fin Ks),
          (∃ j, (src e = v ∧ ψ e = some (c, i, j)) ∨ (tgt e = v ∧ ψ e = some (c, j, i))) →
          (∃ j, (src e' = v ∧ ψ e' = some (c, i, j)) ∨ (tgt e' = v ∧ ψ e' = some (c, j, i))) →
          e = e') ∧
        -- the large edges left unchosen carry little more weight than their unassigned fractions
        ∀ v, ∑ e ∈ (G.inc v).filter (fun e => β ≤ G.w e ∧ ψ e = none), G.w e ≤
          ∑ e ∈ (G.inc v).filter (fun e => β ≤ G.w e),
            G.w e * (1 - ∑ c, ∑ i, ∑ j, XL e c i j) + ε * n + K * n ^ (2 / 3 : ℝ) := by sorry

end WeightedEdgeColor
