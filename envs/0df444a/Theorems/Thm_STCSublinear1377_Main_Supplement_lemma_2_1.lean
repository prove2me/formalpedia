-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_lemma_2_1
-- name    : STCSublinear1377.Main.Supplement.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:22:33.233304+00:00
-- url     : https://prove2.me/theorems/c1fb35d1-0fdc-44d1-9e09-765a58c5951f
-- title:
--   Lemma 2.1 — Fewer than 2n/D hubs at a threshold D ≥ 4k
-- statement:
--   Let $G$ be a connected simple unweighted graph on $n\ge2$ vertices with spanning tree congestion $k$, let $D$ be a real threshold and $H=\{v:d_G(v)>D\}$ the set of hubs, $q=|H|$. If $D\ge4k$, then
--
--   $$q<\frac{2n}{D}\qquad\text{and}\qquad q<n .$$
--
--   The bound on the number of hubs feeds the ratio estimate (2.3) of the simple algorithm.
--
--   Differences from the source:
--   - generalization: the standing assumption 1 ≤ q of §2 → every q, including q = 0; reason: for q = 0 both inequalities hold because D ≥ 4k ≥ 4 > 0; the source case 1 ≤ q is included
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Lemma 2.1, PDF/printed p.4

import Definitions.Def_STCSublinear1377_Main_Laminar
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Lemma 2.1: at a threshold `D ≥ 4k` there are fewer than `2n/D` (hence fewer than `n`) hubs. -/
theorem lemma_2_1 :
    ∀ n : ℕ, 2 ≤ n → ∀ g : Table n, isInput g → ∀ D : ℝ, 4 * (stc g : ℝ) ≤ D →
      ((hubs (original g) D).card : ℝ) < 2 * (n : ℝ) / D ∧
        (hubs (original g) D).card < n := by sorry

end STCSublinear1377.Main.Supplement
