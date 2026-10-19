-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_lemma_A_1
-- name    : ShapeMoment.LogConcave.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:14.764473+00:00
-- url     : https://prove2.me/theorems/c2c7ef4d-8217-434b-9e2d-fa9c965c3c52
-- title:
--   Lemma A.1 — convex non-strict power region
-- statement:
--   For positive integers $u$ and $v$,
--
--   $$\{(x,y,z)\in\mathbb R_{\ge0}^3:x^uy^v\ge z^{u+v}\}\text{ is convex}.$$
--
--   This is the preliminary non-strict result behind Proposition 2.5.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 24, Lemma A.1

import Mathlib

namespace ShapeMoment.LogConcave

theorem lemma_A_1 (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    Convex ℝ {p : ℝ × ℝ × ℝ |
      p.2.2 ^ (u + v) ≤ p.1 ^ u * p.2.1 ^ v ∧
      0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2} := by sorry

end ShapeMoment.LogConcave
