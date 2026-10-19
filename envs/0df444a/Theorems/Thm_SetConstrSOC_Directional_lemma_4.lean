-- Prove2me | Theorems.Thm_SetConstrSOC_Directional_lemma_4
-- name    : SetConstrSOC.Directional.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:26.487763+00:00
-- url     : https://prove2.me/theorems/f6f65a09-9516-41e9-8e72-519422797943
-- title:
--   Lemma 4 — critical directions have zero first derivative
-- statement:
--   Let $\bar x$ be a locally optimal feasible solution of (P). If $g(x)-\Lambda$ is metrically subregular at $(\bar x,0)$ in a critical direction $d\in C(\bar x)$, then
--
--   $$
--   \nabla f(\bar x)d=0.
--   $$
--
--   This lets the primal second-order condition apply to the critical directions used in Theorem 2.
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, p. 13, Lemma 4

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

namespace SetConstrSOC.Directional

/-- Lemma 4, p. 13: a critical direction has zero first derivative. -/
theorem lemma_4 {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (x : E n) (hmin : IsLocalMinOn P.f P.feasible x) (hx : x ∈ P.feasible)
    (d : E n) (hd : d ∈ P.criticalCone x)
    (hMS : MetricSubregularDirAt P.g P.Λ x d) :
    (fderiv ℝ P.f x) d = 0 := by sorry

end SetConstrSOC.Directional
