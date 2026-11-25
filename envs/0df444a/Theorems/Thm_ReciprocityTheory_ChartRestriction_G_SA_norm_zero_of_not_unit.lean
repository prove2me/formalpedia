-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_norm_zero_of_not_unit
-- name    : ReciprocityTheory.ChartRestriction.G.SA.norm_zero_of_not_unit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:44.205574+00:00
-- url     : https://prove2.me/theorems/69e515b1-f7f9-45c6-a8ec-9e1f8b80ecca
-- title:
--   SA: norm zero of not unit
-- statement:
--   The SA construction uses the norm zero of not unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ExistsMaxOfNotCoprime.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ExistsMaxOfNotCoprime.lean#L10-L13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
variable {K : Type*} [CommRing K] {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x)
include hσ hfix

theorem ReciprocityTheory.ChartRestriction.G.SA.norm_zero_of_not_unit {z : K} (hz : ¬ IsUnit z) : z * σ z = 0 := by sorry
