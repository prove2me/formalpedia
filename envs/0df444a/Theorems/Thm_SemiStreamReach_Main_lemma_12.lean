-- Prove2me | Theorems.Thm_SemiStreamReach_Main_lemma_12
-- name    : SemiStreamReach.Main.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:51:34.526937+00:00
-- url     : https://prove2.me/theorems/a4098441-93f7-4c44-a1aa-f4f85a1dd6f1
-- title:
--   Lemma 12 — scaling and rounding: $\alpha=\varepsilon\Delta/h$, $R=\lceil 4h/\varepsilon\rceil$ preserve distances up to $1+2\varepsilon$
-- statement:
--   Let $G$ be a weighted directed graph on a finite vertex set $V$ with positive edge weights, let $h\ge1$ be an integer and $0<\varepsilon\le 1/2$ (the standing assumption of §3), and let $H$ be an $(h,\varepsilon)$-hopset of $G$. Let $s\in V$ and let $\Delta>0$ be a distance guess. Put $\alpha=\varepsilon\Delta/h$ and $R=\lceil 4h/\varepsilon\rceil$, and let $G_\alpha\cup H_\alpha$ be the union of the rounded graphs (each edge $e$ of weight $\lceil w(e)/\alpha\rceil$). Then every vertex $v$ satisfies
--   $$\alpha\cdot \mathrm{dist}_{G_\alpha\cup H_\alpha}(s,v)\ \ge\ \mathrm{dist}_G(s,v),$$
--   and if moreover $\Delta\le \mathrm{dist}_G(s,v)<2\Delta$, then $\mathrm{dist}_{G_\alpha\cup H_\alpha}(s,v)\le R$ and $\alpha\cdot\mathrm{dist}_{G_\alpha\cup H_\alpha}(s,v)\le(1+2\varepsilon)\,\mathrm{dist}_G(s,v)$.
--
--   This is the reduction of Klein and Subramanian: with a hopset, approximate distances only require exact distances up to radius $O(h/\varepsilon)$ in $O(\log n)$ rounded graphs, which is what the streaming algorithm computes with BatchedDijkstra.
--
--   Differences from the source:
--   - generalization: standing assumptions of §3 (p. 13): polynomial aspect ratio, m ≥ n, 1/ε = O(log^{c0} n) → only positive weights, h ≥ 1 and 0 < ε ≤ 1/2 are assumed; reason: the statement and its proof (inequality (2) and Definition 11) use none of them; the Lean statement specializes to the paper's graphs
--   - encoding: real positive weights, distances ∞ for unreachable pairs, G_α ∪ H_α keeping the lightest edge → weights in ℝ≥0∞ (⊤ = no edge), dist in ℝ≥0∞, union = rounded G α ⊓ rounded H α, α·dist as ENNReal.ofReal α * dist; reason: Lean convention; same instances
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 14 (PDF 16), Lemma 12

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Lemma 12 (Scaling and rounding [KS97]), p. 14 (PDF 16), with the standing assumptions of §3
(p. 13): positive edge weights and `ε ≤ 1/2`. `H` is an `(h, ε)`-hopset of `G` (Definition 11),
`α = εΔ/h`, `R = ⌈4h/ε⌉`, and `G_α ∪ H_α` is `rounded G α ⊓ rounded H α`. -/
theorem lemma_12 {V : Type*} [Fintype V] (G H : WGraph V) (h : ℕ) (ε : ℝ) (s : V) (Δ : ℝ)
    (hG : PositiveWeights G) (hh : 1 ≤ h) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (hH : IsHopset G H h ε) (hΔ : 0 < Δ) :
    ∀ v : V,
      dist G s v ≤
          ENNReal.ofReal (ε * Δ / h) * dist (rounded G (ε * Δ / h) ⊓ rounded H (ε * Δ / h)) s v ∧
        ((ENNReal.ofReal Δ ≤ dist G s v ∧ dist G s v < ENNReal.ofReal (2 * Δ)) →
          dist (rounded G (ε * Δ / h) ⊓ rounded H (ε * Δ / h)) s v ≤
              ((⌈4 * (h : ℝ) / ε⌉₊ : ℕ) : ℝ≥0∞) ∧
            ENNReal.ofReal (ε * Δ / h) *
                dist (rounded G (ε * Δ / h) ⊓ rounded H (ε * Δ / h)) s v ≤
              ENNReal.ofReal (1 + 2 * ε) * dist G s v) := by sorry

end SemiStreamReach.Main
