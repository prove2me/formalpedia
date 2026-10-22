-- Prove2me | Theorems.Thm_PrefSemimetric_TopDiff_dmu_axiom4
-- name    : PrefSemimetric.TopDiff.dmu_axiom4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:34.122601+00:00
-- url     : https://prove2.me/theorems/7979c59c-6823-433e-aa78-1cc9335eb9f0
-- title:
--   §3.3, p. 17 — every D^µ satisfies Axiom 4
-- statement:
--   Let $X$ be a finite set and $\mu$ a positive measure on $2^X$. If $\succsim$ and $\trianglerighteq$ are acyclic orders with the same asymmetric part ($\succ=\vartriangleright$), then
--   $$D^\mu(\succsim,\trianglerighteq)=0.$$
--
--   Maximal elements depend only on the strict part of a relation, so $D^\mu$ cannot distinguish orders that differ only in their symmetric parts.
--
--   **Formalization Note** $\mu$ is given by point weights $w\ge0$.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, p. 17, §3.3 ('Finally, it is plain that Dµ satisfies Axiom 4.'); Axiom 4, p. 15

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

namespace PrefSemimetric.TopDiff

theorem dmu_axiom4 {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    Axiom4 (Dmu w) := by sorry

end PrefSemimetric.TopDiff
