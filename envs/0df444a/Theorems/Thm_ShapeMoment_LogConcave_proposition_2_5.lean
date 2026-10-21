-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_proposition_2_5
-- name    : ShapeMoment.LogConcave.proposition_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:14.61556+00:00
-- url     : https://prove2.me/theorems/407079e4-9497-4a31-a23b-60273dc7143e
-- title:
--   Proposition 2.5 — convex strict power region
-- statement:
--   For positive integers $u$ and $v$,
--
--   $$\{(x,y,z)\in\mathbb R_{\ge0}^3:x^uy^v>z^{u+v}\}\text{ is convex}.$$
--
--   This supplies the convex forbidden region associated with a log-concavity inequality.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 6, Proposition 2.5; proof p. 24

import Mathlib

namespace ShapeMoment.LogConcave

theorem proposition_2_5 (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    Convex ℝ {p : ℝ × ℝ × ℝ |
      p.2.2 ^ (u + v) < p.1 ^ u * p.2.1 ^ v ∧
      0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2} := by sorry

end ShapeMoment.LogConcave
