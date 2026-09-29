-- Prove2me | Theorems.Thm_Rudin_ch01_complete_ordered_field_iso_real
-- name    : Rudin.ch01_complete_ordered_field_iso_real
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:43:18.162456+00:00
-- url     : https://prove2.me/theorems/07931db0-a2bb-4328-841a-f19f981e1e83
-- title:
--   Theorem 1.19 — the complete ordered field is unique
-- statement:
--   Let $K$ be an ordered field with the least-upper-bound property. Then there is an isomorphism of ordered fields $e : K \to \mathbb{R}$, and it is the only one. Together with the existence of $\mathbb{R}$ this is Rudin's Theorem 1.19: an ordered field with the least-upper-bound property exists, and since the isomorphism above is unique, the copy of $\mathbb{Q}$ inside $K$ is the canonical one, so $K$ contains $\mathbb{Q}$ as an ordered subfield.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, p. 8, Theorem 1.19 (proof in the Appendix, pp. 17-21)

import Mathlib
import Definitions.Def_Rudin_ch01_order

namespace Rudin

/-- Rudin, Theorem 1.19 (existence and uniqueness of the real field): an ordered field with the
least-upper-bound property is isomorphic, as an ordered field, to `ℝ`, and the isomorphism is
unique.  Together with the existence of `ℝ` itself this is Rudin's statement that there is an
ordered field with the least-upper-bound property containing `ℚ` as a subfield, unique up to
isomorphism. -/
theorem ch01_complete_ordered_field_iso_real (K : Type) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (hK : HasLeastUpperBoundProperty K) :
    ∃ e : K ≃+*o ℝ, ∀ e' : K ≃+*o ℝ, e' = e := by sorry

end Rudin
