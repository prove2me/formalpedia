-- Prove2me | Theorems.Thm_Rudin_ch01_glb_from_lub
-- name    : Rudin.ch01_glb_from_lub
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:22:37.060574+00:00
-- url     : https://prove2.me/theorems/64d19e9b-6e3e-42b6-9424-c29bc39b3a20
-- title:
--   Theorem 1.11 — the least-upper-bound property implies the greatest-lower-bound property
-- statement:
--   Let $S$ be an ordered set with the least-upper-bound property and let $B \subseteq S$ be nonempty and bounded below. Let $L$ be the set of lower bounds of $B$. Then $\sup L$ exists and equals $\inf B$: there is an element $x$ that is simultaneously the least upper bound of $L$ and the greatest lower bound of $B$. Consequently every ordered set with the least-upper-bound property automatically has the greatest-lower-bound property.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, p. 5, Theorem 1.11

import Mathlib
import Definitions.Def_Rudin_ch01_order

namespace Rudin

/-- Rudin, Theorem 1.11: an ordered set with the least-upper-bound property also has the
greatest-lower-bound property, and the infimum of a set `B` bounded below is the supremum
of the set of lower bounds of `B`. -/
theorem ch01_glb_from_lub {S : Type*} [LinearOrder S]
    (hS : HasLeastUpperBoundProperty S) (B : Set S) (hne : B.Nonempty) (hbdd : BddBelow B) :
    ∃ x : S, IsLUB (lowerBounds B) x ∧ IsGLB B x := by sorry

end Rudin
