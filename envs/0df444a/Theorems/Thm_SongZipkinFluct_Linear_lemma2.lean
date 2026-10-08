-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_lemma2
-- name    : SongZipkinFluct.Linear.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:33.411733+00:00
-- url     : https://prove2.me/theorems/ab8e5b08-bba2-4d48-a3a3-6c43373e0f43
-- title:
--   Lemma 2 — coercivity of C and G⁺
-- statement:
--   For every world state $i$, the expected lead-time inventory cost diverges at both ends of the integer line, and the myopic cost diverges as the inventory position increases. Under $\alpha\bar c<p$, the myopic cost also diverges as the position decreases.
--
--   $$C(i,y)\to+\infty\ (|y|\to\infty),\qquad G^+(i,y)\to+\infty\ (y\to+\infty),\qquad G^+(i,y)\to+\infty\ (y\to-\infty)\text{ if }\alpha\bar c<p.$$
--
--   These limits yield finite minimizers when Assumption 1 holds.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 355, Lemma 2, (3)–(5)

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Model

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Lemma 2, p. 355, displays (3)--(5).
The negative-end divergence of `G⁺` alone needs Assumption 1. -/
theorem lemma2 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) :
    ∀ i : I, CoerciveInt (M.C i) ∧
      Filter.Tendsto (M.Gplus i) Filter.atTop Filter.atTop ∧
      (M.Assumption1 → Filter.Tendsto (M.Gplus i) Filter.atBot Filter.atTop) := by sorry

end SongZipkinFluct.Linear
