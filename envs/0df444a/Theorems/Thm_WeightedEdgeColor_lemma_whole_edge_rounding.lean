-- Prove2me | Theorems.Thm_WeightedEdgeColor_lemma_whole_edge_rounding
-- name    : WeightedEdgeColor.lemma_whole_edge_rounding
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T05:57:07.89534+00:00
-- url     : https://prove2.me/theorems/fb450809-32cc-4fcf-852a-dafa016f4f34
-- title:
--   Rounding fractional options with slack to whole edges (proof of Theorem 3.1)
-- statement:
--   This is the last step in the proof of Theorem 3.1 (local-to-global rounding): fractional placement options with spare capacity are turned into a feasible partial coloring that loses almost no weight.
--
--   Fix constants $C_1>0$, $0<\sigma<1$, $0<\beta\le r_0\le1$ with $2\beta\le\sigma r_0$, $C_m>0$, $\varepsilon>0$, and an integer $K_s\ge0$ (slots per profile). Let $G$ be a finite simple graph with weights $w:E\to(0,1]$. Let $n$ be a real parameter with $W_G(v)\le n$ for every vertex, and let $\mathcal C$ be a palette with $|\mathcal C|\le C_1n$.
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
--   Then, for all sufficiently large $n$, there is a feasible partial coloring $\varphi$ in which an edge $e$ receives only colors $c$ with $m_{e,c}>0$. At every vertex $v$ its colored weight satisfies
--
--   $$
--   \sum_{e\ni v,\ e\text{ colored}}w_e\;\ge\;\sum_{e\ni v}w_e\,s_e-\varepsilon n-O\big(n^{2/3}\big).
--   $$
--
--   The threshold and the implied constant depend only on the fixed constants, not on the number of vertices or the minimum edge weight.
--
--   In the source this is the passage from the fractions $\hat X(e,c,i,j)$ to whole edges: the rounding of large edges with extra slots, the rounding of small edges, and the final error count.
--
--   **Formalization Note.** The orientation is given by maps `src`, `tgt` with $\{u_e,v_e\}$ equal to the ends of $e$. Slots are indexed by `Fin Ks`; the source uses $K=\lfloor1/\beta\rfloor$ slots. The load of slot $i$ at $(v,c)$ sums $X^L(e,c,i,\cdot)$ over edges with $u_e=v$ and $X^L(e,c,\cdot,i)$ over edges with $v_e=v$. The threshold $n_0$ and the constant $K$ of $O(n^{2/3})$ are chosen before the graph.
-- source:
--   R. Gajjala, A. Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, arXiv:2611.03190 (preprint of November 2, 2026), proof of Theorem 3.1, pp.40-43: from 'An edge may currently have total assigned fraction S_e > 1 ... call the new fractions X^' through 'Rounding the large edges', 'Rounding the small edges' and the final error calculation (C.13)

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets

set_option autoImplicit false
namespace WeightedEdgeColor

theorem lemma_whole_edge_rounding (C₁ σ r₀ β Cm ε : ℝ) (Ks : ℕ)
    (hC₁ : 0 < C₁) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    (hβ0 : 0 < β) (hβ : β ≤ r₀) (hβσ : 2 * β ≤ σ * r₀) (hCm : 0 < Cm) (hε : 0 < ε) :
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ (b : V → 𝒞 → Fin Ks → ℝ) (R : V → 𝒞 → ℝ) (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ)
        (XS : E → 𝒞 → ℝ),
      -- valid profiles: slots `b v c i ≥ 0`, reserve `R v c ≥ 0`, total size at most one,
      -- every positive reserve at least `r₀`
      (∀ v c, (∀ i, 0 ≤ b v c i) ∧ 0 ≤ R v c ∧ ∑ i, b v c i + R v c ≤ 1 ∧ (R v c = 0 ∨ r₀ ≤ R v c))  →
      -- nonnegative option fractions
      (∀ e c i j, 0 ≤ XL e c i j) →
      (∀ e c, 0 ≤ XS e c) →
      -- large options use slots that can hold the edge, at both ends
      (∀ e c i j, XL e c i j ≠ 0 → β ≤ G.w e ∧ G.w e ≤ b (src e) c i ∧ G.w e ≤ b (tgt e) c j)  →
      -- small options use positive reserves at both ends
      (∀ e c, XS e c ≠ 0 → G.w e < β ∧ 0 < R (src e) c ∧ 0 < R (tgt e) c)  →
      -- each edge has total fraction at most one, and at most `Cm / n` in each color
      (∀ e, ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) ≤ 1)  →
      (∀ e c, ∑ i, ∑ j, XL e c i j + XS e c ≤ Cm / n)  →
      -- slack in every slot and every reserve
      (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
         + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ)  →
      (∀ v c, ∑ e ∈ G.inc v, G.w e * XS e c ≤ (1 - σ) * R v c) →
      ∃ φ : E → Option 𝒞, G.IsFeasiblePartialColoring φ ∧
        (∀ e c, φ e = some c → 0 < ∑ i, ∑ j, XL e c i j + XS e c) ∧
        ∀ v, (∑ e ∈ G.inc v, G.w e * ∑ c, (∑ i, ∑ j, XL e c i j + XS e c)) - ε * n
          - K * n ^ (2 / 3 : ℝ) ≤ G.coloredWeight φ v := by sorry

end WeightedEdgeColor
