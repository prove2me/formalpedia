-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_division_distance_angle
-- name    : SmoothedSimplex.Shadow.division_distance_angle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:47:45.571981+00:00
-- url     : https://prove2.me/theorems/c19468ca-b1ba-4667-b1fb-e410c8cb9e2f
-- title:
--   Lemma 4.0.12 — division into distance and angle
-- statement:
--   Let $x\in\mathbb R^d$, let $0<s\le 2$, and let $q$ and $\omega$ be unit vectors satisfying
--
--   1. $\langle\omega\,|\,x-sq\rangle=0$, and
--   2. $\mathrm{dist}(x,sq)\le 4\sqrt2$.
--
--   Then
--
--   $$
--   \mathrm{angle}(q,x)\ \ge\ \frac{\mathrm{dist}(x,sq)\,\langle\omega|q\rangle}{2+4\sqrt2}.
--   $$
--
--   This deterministic estimate splits the angle between the objective direction and a point of the facet into a distance factor (studied in Section 4.1) and an angle-of-incidence factor $\langle\omega|q\rangle$ (studied in Section 4.2).
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.0.12, printed pp. 44–45 (PDF pp. 44–45)

import Mathlib

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 4.0.12 (Division into distance and angle)** (Spielman & Teng, arXiv:cs/0111050v7,
Lemma 4.0.12, printed pp. 44–45, PDF pp. 44–45). Let `x` be a vector, let `0 < s ≤ 2`, and let
`q` and `ω` be unit vectors satisfying (a) `⟨ω|x − sq⟩ = 0`, and (b) `dist(x, sq) ≤ 4√2`.
Then `angle(q, x) ≥ dist(x, sq) ⟨ω|q⟩ / (2 + 4√2)`.

**Formalization Note.** `x, q, ω ∈ ℝ^d`; `angle` is `InnerProductGeometry.angle` (in `[0, π]`). -/
theorem division_distance_angle {d : ℕ} (x q ω : EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (hs0 : 0 < s) (hs2 : s ≤ 2) (hq : ‖q‖ = 1) (hω : ‖ω‖ = 1)
    (ha : ⟪ω, x - s • q⟫ = 0) (hb : dist x (s • q) ≤ 4 * Real.sqrt 2) :
    dist x (s • q) * ⟪ω, q⟫ / (2 + 4 * Real.sqrt 2) ≤ InnerProductGeometry.angle q x := by sorry

end SmoothedSimplex.Shadow
