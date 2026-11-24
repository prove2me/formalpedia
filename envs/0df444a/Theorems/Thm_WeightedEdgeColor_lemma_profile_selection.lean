-- Prove2me | Theorems.Thm_WeightedEdgeColor_lemma_profile_selection
-- name    : WeightedEdgeColor.lemma_profile_selection
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T05:57:09.66991+00:00
-- url     : https://prove2.me/theorems/4737c7ff-dc43-4c43-9dbb-9a4c89ee1963
-- title:
--   Choosing profiles and fractional options with slack (proof of Theorem 3.1)
-- statement:
--   This is the first part of the proof of Theorem 3.1 (local-to-global rounding): from locally feasible proposals it builds coordinated fractional placement options with spare capacity in every slot, losing only $\varepsilon n+O(n^{3/4})$ proposed weight at each vertex.
--
--   Fix constants $C_0,C_1,\varepsilon>0$ and an integer $r$. There are constants $0<\sigma<1$, $0<\beta\le r_0\le1$ with $2\beta\le\sigma r_0$, $C_m>0$ and an integer $K_s$, depending only on $C_0,C_1,\varepsilon,r$, with the following property for all sufficiently large $n$.
--
--   Let $G$ be a finite simple graph with weights in $(0,1]$ whose vertices are divided into $r$ groups with no edge inside a group. Let $n$ be a real parameter with $W_G(v)\le n$ for every vertex, and let $\mathcal C$ be a palette with $|\mathcal C|\le C_1n$. Let proposals $x_{e,c}$ satisfy, for every edge $e$, color $c$ and vertex $v$,
--
--   $$
--   0\le x_{e,c}\le\frac{C_0}{n},\qquad\sum_{c}x_{e,c}\le1,\qquad(x_{e,c}:e\ni v)\in\mathcal K_v .
--   $$
--
--   Then there are profiles and fractional options, as described below, that satisfy conditions 1–3, use only pairs with $x_{e,c}>0$, and satisfy at every vertex
--
--   $$
--   \sum_{e\ni v}w_e\,s_e\;\ge\;\sum_{e\ni v}w_e\sum_{c}x_{e,c}-\varepsilon n-O\big(n^{3/4}\big).
--   $$
--
--   **Profiles and options.** Every edge $e$ is oriented as $e=(u_e,v_e)$. At every vertex $v$ and color $c$ a *profile* is given: slot sizes $b_{v,c,1},\dots,b_{v,c,K_s}\ge0$ and a reserved space $R_{v,c}\ge0$ for small edges, with
--
--   $$
--   \sum_i b_{v,c,i}+R_{v,c}\le1,\qquad R_{v,c}=0\ \text{ or }\ R_{v,c}\ge r_0 .
--   $$
--
--   A *large option* $X^L(e,c,i,j)\ge0$ is a fraction of edge $e$ that would receive color $c$ and occupy slot $i$ of the profile at $(u_e,c)$ and slot $j$ of the profile at $(v_e,c)$. A *small option* $X^S(e,c)\ge0$ is a fraction of $e$ that would receive color $c$ and use the reserved spaces at both ends. Write
--
--   $$
--   m_{e,c}=\sum_{i,j}X^L(e,c,i,j)+X^S(e,c),\qquad s_e=\sum_c m_{e,c}.
--   $$
--
--   The options satisfy the following conditions.
--
--   1. *Compatibility.* $X^L(e,c,i,j)>0$ only if $w_e\ge\beta$, $w_e\le b_{u_e,c,i}$ and $w_e\le b_{v_e,c,j}$. $X^S(e,c)>0$ only if $w_e<\beta$, $R_{u_e,c}>0$ and $R_{v_e,c}>0$.
--   2. *Small fractions.* $s_e\le1$ for every edge, and $m_{e,c}\le C_m/n$ for every edge and color.
--   3. *Slack.* Every slot has total fraction (over the edges at either end that use it) at most $1-\sigma$. Every reserved space has weighted load $\sum_{e\ni v}w_eX^S(e,c)\le(1-\sigma)R_{v,c}$.
--
--   In the source these are the profile lists chosen one group at a time and the fractions $\hat X(e,c,i,j)$ after an edge's total is clipped to one. Capacity slack and inequality (C.11) are the properties stated here.
--
--   **Formalization Note.** The orientation `src`, `tgt` of the edges is arbitrary and given as input. The constants $\sigma,r_0,\beta,C_m,K_s$ are produced before the threshold $n_0$ and the constant $K$ of $O(n^{3/4})$, and all are chosen before the graph. Slots are indexed by `Fin Ks`.
-- source:
--   R. Gajjala, A. Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, arXiv:2611.03190 (preprint of November 2, 2026), proof of Theorem 3.1, pp.36-40: 'Profiles and lost weight', 'Choosing profiles group by group' (C.5)-(C.10), load bounds p.40, clipping and (C.11) p.40

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets

set_option autoImplicit false
namespace WeightedEdgeColor

theorem lemma_profile_selection (C₀ C₁ ε : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hε : 0 < ε)
    (r : ℕ) :
    ∃ (σ r₀ β Cm : ℝ) (Ks : ℕ), 0 < σ ∧ σ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < β ∧ β ≤ r₀ ∧
      2 * β ≤ σ * r₀ ∧ 0 < Cm ∧
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ g : V → Fin r,
      (∀ (e : E) (u v : V), G.ends e = s(u, v) → g u ≠ g v) →
      ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ x : E → 𝒞 → ℝ, (∀ e c, 0 ≤ x e c ∧ x e c ≤ C₀ / n) → (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, G.InK v (fun e => x e c)) →
      ∃ (b : V → 𝒞 → Fin Ks → ℝ) (R : V → 𝒞 → ℝ) (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ)
        (XS : E → 𝒞 → ℝ),
      -- valid profiles: slots `b v c i ≥ 0`, reserve `R v c ≥ 0`, total size at most one,
      -- every positive reserve at least `r₀`
      (∀ v c, (∀ i, 0 ≤ b v c i) ∧ 0 ≤ R v c ∧ ∑ i, b v c i + R v c ≤ 1 ∧ (R v c = 0 ∨ r₀ ≤ R v c)) ∧
      -- nonnegative option fractions
      (∀ e c i j, 0 ≤ XL e c i j) ∧
      (∀ e c, 0 ≤ XS e c) ∧
      -- large options use slots that can hold the edge, at both ends
      (∀ e c i j, XL e c i j ≠ 0 → β ≤ G.w e ∧ G.w e ≤ b (src e) c i ∧ G.w e ≤ b (tgt e) c j) ∧
      -- small options use positive reserves at both ends
      (∀ e c, XS e c ≠ 0 → G.w e < β ∧ 0 < R (src e) c ∧ 0 < R (tgt e) c) ∧
      -- each edge has total fraction at most one, and at most `Cm / n` in each color
      (∀ e, ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) ≤ 1) ∧
      (∀ e c, ∑ i, ∑ j, XL e c i j + XS e c ≤ Cm / n) ∧
      -- slack in every slot and every reserve
      (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
         + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ) ∧
      (∀ v c, ∑ e ∈ G.inc v, G.w e * XS e c ≤ (1 - σ) * R v c) ∧
      -- options only where the proposal is positive
      (∀ e c, ∑ i, ∑ j, XL e c i j + XS e c ≠ 0 → 0 < x e c) ∧
      -- almost all proposed weight survives at every vertex
      ∀ v, (∑ e ∈ G.inc v, G.w e * ∑ c, x e c) - ε * n - K * n ^ (3 / 4 : ℝ) ≤
        ∑ e ∈ G.inc v, G.w e * ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) := by sorry

end WeightedEdgeColor
