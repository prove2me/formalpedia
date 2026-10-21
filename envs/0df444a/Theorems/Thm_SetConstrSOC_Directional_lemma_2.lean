-- Prove2me | Theorems.Thm_SetConstrSOC_Directional_lemma_2
-- name    : SetConstrSOC.Directional.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:49.018283+00:00
-- url     : https://prove2.me/theorems/c2c4fbd3-eef1-4265-8a94-5ae00e9c1626
-- title:
--   Lemma 2 — distance to the outer limit
-- statement:
--   Let $C$ be a set-valued map from $\mathbb R^m$ to subsets of $\mathbb R^n$, and fix $u\in\mathbb R^m$ and $x\in\mathbb R^n$. Then
--
--   $$
--   \liminf_{u'\to u}\operatorname{dist}(x,C(u'))
--   =\operatorname{dist}\bigl(x,\limsup_{u'\to u}C(u')\bigr).
--   $$
--
--   This identity connects distance estimates with the outer limits used to define tangent sets.
--
--   **Formalization Note** Distances take values in $[0,+\infty]$, so distance to an empty set is $+\infty$.
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, p. 10, Lemma 2

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

open Filter
open scoped Topology

namespace SetConstrSOC.Directional

/-- Lemma 2, p. 10: distance commutes with the outer limit through a liminf. -/
theorem lemma_2 {m n : ℕ} (C : E m → Set (E n)) (u : E m) (x : E n) :
    Filter.liminf (fun u' => EMetric.infEdist x (C u')) (𝓝 u) =
      EMetric.infEdist x (outerLimit C u) := by sorry

end SetConstrSOC.Directional
