-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_prop_C_3
-- name    : PinwheelDensity.ExactRange.prop_C_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:55.265008+00:00
-- url     : https://prove2.me/theorems/99ddc9c8-6bda-4120-87aa-31bd15eb0254
-- title:
--   Proposition C.3 — both split-tree modes are sound
-- statement:
--   Let $\beta\in\mathbb Q$ and let $(\ell,u)$ be a box of rational lists. If a split tree is valid for this box, in either unsorted or sorted mode, then every nondecreasing member $b$ of the box, meaning $\ell\le b\le u$ componentwise, $b>0$ and $D(b)<\beta$, is schedulable as a list of rational periods.
--
--   No relation between the tree, the box and $\beta$ is assumed beyond validity. This is the soundness of tree certificates, the first of the two certificate types of a run.
--
--   Differences from the source:
--   - encoding: the word test for $r_i=p/q$ with positive integers $p,q$ → $p/q$ in lowest terms via `Rat.num` and `Rat.den`; reason: both inequalities of the test scale with $(p,q)$, so every representation gives the same test
--   - encoding: a split at position $i$ → a position out of range is rejected; reason: the condition $\ell_i<x<u_i$ refers to entries that must exist
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Proposition C.3, p. 14 (PDF p. 14)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf
import Definitions.Def_PinwheelDensity_ExactRange_checkRun

namespace PinwheelDensity.ExactRange

/-- Proposition C.3, p. 14: if a split tree is valid for a box, in either mode, every sorted member
of the box is schedulable. -/
theorem prop_C_3 (sortedMode : Bool) (β : ℚ) (T : SplitTree) (ℓ u : List ℚ)
    (hT : checkTree sortedMode β T ℓ u = true) (b : List ℚ) (hb : b.Pairwise (· ≤ ·))
    (hmem : IsBoxMember ℓ u β b) : RatSchedulable b := by sorry

end PinwheelDensity.ExactRange
