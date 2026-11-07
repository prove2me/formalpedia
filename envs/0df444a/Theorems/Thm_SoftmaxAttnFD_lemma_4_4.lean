-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_4_4
-- name    : SoftmaxAttnFD.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:38.106164+00:00
-- url     : https://prove2.me/theorems/365b98d7-8c2b-4c16-bc15-e4b8f2810116
-- title:
--   Lemma 4.4, p.16 — radial shell
-- statement:
--   Let $C=\mathrm{conv}\{k_1,\dots,k_n\}\subset\mathbb R^2$ have the origin in its interior, and write each nonzero key as $k_j=\rho_jk_j^\partial$ with $0<\rho_j\le1$ and $k_j^\partial$ on the boundary of $C$. Let $L>0$, $h=\max_jq\cdot k_j$ and
--   $$K_i=\Bigl\{j:\ k_j\ne0,\ \rho_j\ge1-\frac Lh,\ q\cdot k_j^\partial\ge h-L\Bigr\}.$$
--   If $h>L$, then
--   $$\{j:q\cdot k_j\ge h-L\}\subseteq K_i\subseteq\{j:q\cdot k_j\ge h-2L\}.$$
--   Thus a range in radial and boundary coordinates captures all near-maximal keys and widens the score window by at most a factor two.
--
--   Differences from the source:
--   - generalization: the rounded, centered keys of §4.2, with the origin the area centroid → any real keys with the origin interior to their hull; reason: the proof uses only the origin being interior; the page's polygon is an instance
--   - encoding: L = Θ(log(N/η_row)), a positive window → any L > 0; n ≥ 1; reason: the lemma holds for every positive L, and a maximum needs a nonempty index set
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 4.4, p.16

import Mathlib

namespace SoftmaxAttnFD

/-- **Lemma 4.4** (arXiv:2611.06055, sha256 a60f7609…, p.16). The polar coordinates are
`k_j = ρ_j k^∂_j`, `0 < ρ_j ≤ 1`, with `k^∂_j` on the boundary of `C`, for each nonzero key, and
`K_i = {j : k_j ≠ 0, ρ_j ≥ 1 − L/h_i, q_i·k^∂_j ≥ h_i − L}`. For `h_i > L`,
`{j : q_i·k_j ≥ h_i − L} ⊆ K_i ⊆ {j : q_i·k_j ≥ h_i − 2L}`.

**Formalization Note** `L > 0` is the page's score window (`L = Θ(log(N/η_row))`, p.15). `ρ` and `kb`
are read only at nonzero keys. Since the origin is interior, they are the page's unique ray
coordinates. -/
theorem lemma_4_4 (n : ℕ) (hn : 1 ≤ n) (k : Fin n → Fin 2 → ℝ) (C : Set (Fin 2 → ℝ))
    (hC : C = convexHull ℝ (Set.range k)) (h0 : (0 : Fin 2 → ℝ) ∈ interior C)
    (ρ : Fin n → ℝ) (kb : Fin n → Fin 2 → ℝ)
    (hρ : ∀ j, k j ≠ 0 → 0 < ρ j ∧ ρ j ≤ 1 ∧ k j = ρ j • kb j ∧ kb j ∈ frontier C)
    (q : Fin 2 → ℝ) (h L : ℝ) (hL : 0 < L) (hh : h = ⨆ j, q ⬝ᵥ k j) (hhL : L < h)
    (Ki : Set (Fin n))
    (hKi : Ki = {j | k j ≠ 0 ∧ 1 - L / h ≤ ρ j ∧ h - L ≤ q ⬝ᵥ kb j}) :
    {j | h - L ≤ q ⬝ᵥ k j} ⊆ Ki ∧ Ki ⊆ {j | h - 2 * L ≤ q ⬝ᵥ k j} := by sorry

end SoftmaxAttnFD
