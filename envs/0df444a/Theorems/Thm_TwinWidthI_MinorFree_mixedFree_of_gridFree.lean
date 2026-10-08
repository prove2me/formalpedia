-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_mixedFree_of_gridFree
-- name    : TwinWidthI.MinorFree.mixedFree_of_gridFree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:29.736507+00:00
-- url     : https://prove2.me/theorems/13400490-b0fd-45d2-9676-e0bdaac629d1
-- title:
--   pp. 3:26, 3:29 — a g-grid-free 0/1 matrix is g-mixed free
-- statement:
--   Let $M$ be a Boolean matrix. If it has no $t$-grid minor, then it has no $t$-mixed minor:
--
--   $$
--   M\text{ is }t\text{-grid free}\quad\Longrightarrow\quad M\text{ is }t\text{-mixed free}.
--   $$
--
--   A mixed Boolean zone has a $1$, so every mixed minor is a grid minor with the same cut points. This connects the proof's stronger grid-free conclusion to the mixed-free hypothesis used for twin-width.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:18–3:19, definitions of grid and mixed minors; p. 3:26, proof of Theorem 6.3

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_Setting

namespace TwinWidthI.MinorFree

/-- Every mixed Boolean zone contains a one, so grid freeness implies mixed freeness
(pp. 3:26, 3:29). -/
theorem mixedFree_of_gridFree {n m : ℕ} (M : Matrix (Fin n) (Fin m) Bool)
    (t : ℕ) (h : ¬ TwinWidthI.GridThm.HasGridMinor M t) : TwinWidthI.GridThm.MixedFree M t := by sorry

end TwinWidthI.MinorFree
