-- Prove2me | Theorems.Thm_ValuativeSYZ_lemma_3_6_convex_on_face
-- name    : ValuativeSYZ.lemma_3_6_convex_on_face
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T11:48:33.559339+00:00
-- url     : https://prove2.me/theorems/7a4f9f9a-f6f4-4d95-ab21-34b41d4b9d32
-- title:
--   Lemma 3.6 (convexity part): functions in $P_c$ are convex on each face
-- statement:
--   **Lemma 3.6, convexity part.** The cost function of the paper is convex in its first variable on
--   each face of the essential skeleton; consequently every function of the class $P_c$ is convex on
--   each face. This milestone records the underlying convexity statement: a supremum of a family of
--   functions that are convex on a convex set, uniformly bounded, is convex on that set.
--
--   Convexity on faces is used repeatedly in §3.4–§3.6, where gradients of the potentials at points of
--   the open faces are compared with the Okounkov body.
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 15, Lemma 3.6 (convexity assertion)

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

namespace ValuativeSYZ

/-- **Lemma 3.6 (convexity part).** If the cost function is convex in its first variable on a
convex set — as it is on each face of the essential skeleton — then every function of the
class `P_c` is convex there. -/
theorem lemma_3_6_convex_on_face {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nonempty B] (c : E → B → ℝ) (M : ℝ) (hc : ∀ x p, |c x p| ≤ M)
    (s : Set E) (hs : Convex ℝ s) (hconv : ∀ p, ConvexOn ℝ s fun x => c x p)
    (φ : E → ℝ) (hφ : φ ∈ Pc c) : ConvexOn ℝ s φ := by sorry

end ValuativeSYZ
