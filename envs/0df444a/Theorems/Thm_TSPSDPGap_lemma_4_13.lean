-- Prove2me | Theorems.Thm_TSPSDPGap_lemma_4_13
-- name    : TSPSDPGap.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:41.2796+00:00
-- url     : https://prove2.me/theorems/4dfe8bdd-6fd6-47c2-be84-66e2acdbcab6
-- title:
--   Lemma 4.13 — a trigonometric identity
-- statement:
--   For every real $\theta$ and every natural number $g$,
--   $$
--   (2\cos\theta-2)\sum_{j=1}^{g-1}(g-j)\cos(j\theta)=\cos(g\theta)-g\cos\theta+(g-1).
--   $$
--   With $\theta=\pi i/d$ it shows $a_i\ge0$ in Claim 4.12.
--
--   Differences from the source: none.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Lemma 4.13, p.19

import Mathlib

namespace TSPSDPGap

/-- **Lemma 4.13: a trigonometric identity.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Lemma 4.13, p.19:
"(2 cos(θ) − 2) Σ_{j=1}^{g−1} (g − j) cos(jθ) = cos(gθ) − g cos(θ) + (g − 1)."

**Formalization Note.** For every real `θ` and natural `g`; `Σ_{j=1}^{g−1}` is the sum over
`Finset.Ico 1 g`, and `g − j`, `g − 1` are computed in `ℝ`. -/
theorem lemma_4_13 (θ : ℝ) (g : ℕ) :
    (2 * Real.cos θ - 2) * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ) =
      Real.cos (g * θ) - g * Real.cos θ + ((g : ℝ) - 1) := by sorry

end TSPSDPGap
