-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_upMk_apply_inr
-- name    : ReciprocityTheory.ChartRestriction.G.T0.upMk_apply_inr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:40.063742+00:00
-- url     : https://prove2.me/theorems/593156fd-3de9-5f8f-a36d-ea3e352d0870
-- title:
--   T0: up Mk apply inr
-- statement:
--   The T0 construction uses the up Mk apply inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UpMkApplyInl.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UpMkApplyInl.lean#L16-L17

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

theorem ReciprocityTheory.ChartRestriction.G.T0.upMk_apply_inr {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ))
    (i : Fin (D + 2)) : upMk ab (Sum.inr i) = ab.1 i := by sorry
