-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_upMk_apply_inl
-- name    : ReciprocityTheory.ChartRestriction.G.T0.upMk_apply_inl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:30.02038+00:00
-- url     : https://prove2.me/theorems/a1c781c1-7237-54ae-897a-48b431ce0b0c
-- title:
--   T0: up Mk apply inl
-- statement:
--   The T0 construction uses the up Mk apply inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UpMkApplyInl.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UpMkApplyInl.lean#L13-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0

theorem ReciprocityTheory.ChartRestriction.G.T0.upMk_apply_inl {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ))
    (p : Fin (D + 2) × Fin (N + 1)) : upMk ab (Sum.inl p) = ab.2 (some p) := by sorry
