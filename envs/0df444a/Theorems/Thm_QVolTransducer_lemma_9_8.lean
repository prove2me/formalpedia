-- Prove2me | Theorems.Thm_QVolTransducer_lemma_9_8
-- name    : QVolTransducer.lemma_9_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:40.360451+00:00
-- url     : https://prove2.me/theorems/88cfa7d4-bcea-4de0-b5e3-f74f3f8c1034
-- title:
--   Lemma 9.8 — the clipped Gibbs distribution is $e^{-t}$-close in total variation
-- statement:
--   Let $d\ge1$ and let $K\subseteq\mathbb R^d$ be a convex body with $B_d\subseteq K$. For every inverse temperature $\beta\ge0$, every $t>0$ and every clipping radius $r\ge\sqrt{(2d+3t)/(2\beta)}$,
--
--   $$
--   \|\pi_{\beta,r}-\pi_\beta\|_{\mathrm{TV}}\le e^{-t},
--   $$
--
--   where $\pi_{\beta,r}$ is the Gibbs distribution of the clipped body $K\cap rB_d$ and the total variation distance of two densities is $\frac12\int_{\mathbb R^d}|p-q|$.
--
--   Clipping at radius $r\sim\sqrt{d/\beta}$ therefore changes the target distribution negligibly, which lets the algorithm work inside a ball whose radius tracks the temperature.
--
--   Differences from the source:
--   - encoding: β ∈ [0, ∞] → β ∈ [0, ∞) (a real number); reason: π_∞ is not a density and no finite radius condition involves it; at β = 0 no real r satisfies the radius condition, in the paper and in Lean
--   - encoding: r ≥ √((2d + 3t)/(2β)) → r > 0 and 2d + 3t ≤ 2βr²; reason: equivalent for β > 0; avoids Lean's 1/0 = 0 at β = 0
--   - encoding: "There exists a universal constant c > 0 such that the following holds" → omitted; reason: c occurs nowhere in the conclusion, so the clause is vacuous (paper.md decision 8)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Lemma 9.8, p.57 (PDF p.59)

import Mathlib
import Definitions.Def_QVolTransducer_partitionFn

namespace QVolTransducer

open MeasureTheory

/-- **Clipping the Gibbs distribution** (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Lemma 9.8, p.57 (PDF p.59)).

Let `d ≥ 1` and let `K ⊆ ℝ^d` be a convex body with `B_d ⊆ K`. For every inverse temperature
`β ≥ 0`, every `t > 0` and every clipping radius `r ≥ √((2d + 3t)/(2β))`, the clipped Gibbs
distribution `π_{β,r}` (the Gibbs distribution of `K ∩ rB_d`, Definition 9.15) satisfies
`‖π_{β,r} − π_β‖_TV ≤ exp(−t)`, where the total variation distance of the two densities is
`½ ∫_{ℝ^d} |p − q|`.

**Formalization Note** `r ≥ √((2d + 3t)/(2β))` is written `2d + 3t ≤ 2βr²` with `r > 0`; at `β = 0`
no radius qualifies, as in the paper. `β = ∞` is not a real number and is not covered. The printed
phrase "There exists a universal constant c > 0 such that the following holds" binds no
occurrence of `c` and is omitted. -/
theorem lemma_9_8 (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (β t r : ℝ) (hd : 1 ≤ d)
    (hK : IsCompact K) (hKc : Convex ℝ K) (hBK : Metric.closedBall 0 1 ⊆ K) (hβ : 0 ≤ β)
    (ht : 0 < t) (hr : 0 < r) (hrt : 2 * (d : ℝ) + 3 * t ≤ 2 * β * r ^ 2) :
    (1 / 2) * ∫ x, |gibbsDensity (K ∩ Metric.closedBall 0 r) β x - gibbsDensity K β x| ≤
      Real.exp (-t) := by sorry

end QVolTransducer
