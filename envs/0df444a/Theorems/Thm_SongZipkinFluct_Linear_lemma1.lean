-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_lemma1
-- name    : SongZipkinFluct.Linear.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:34:45.355621+00:00
-- url     : https://prove2.me/theorems/9dcd9ebe-b471-4c9c-8a43-cb79a97fe543
-- title:
--   Lemma 1 — convexity of C and G⁺
-- statement:
--   Fix a world state $i$. The expected lead-time inventory cost and the myopic cost are convex as functions of integer inventory position: their forward differences are nondecreasing.
--
--   $$\Delta C(i,y)\le\Delta C(i,y+1),\qquad \Delta G^+(i,y)\le\Delta G^+(i,y+1)\quad(y\in\mathbb Z).$$
--
--   This supplies the discrete convexity used to identify basestock minimizers.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 355, Lemma 1

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Model

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Lemma 1, p. 355. Convexity is the
monotonicity of integer forward differences, not integer-scaled `ConvexOn`. -/
theorem lemma1 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) :
    ∀ i : I, IntConvex (M.C i) ∧ IntConvex (M.Gplus i) := by sorry

end SongZipkinFluct.Linear
