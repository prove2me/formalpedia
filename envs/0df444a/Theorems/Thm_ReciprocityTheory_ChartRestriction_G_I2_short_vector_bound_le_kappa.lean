-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_short_vector_bound_le_kappa
-- name    : ReciprocityTheory.ChartRestriction.G.I2.short_vector_bound_le_kappa
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:51:33.400948+00:00
-- url     : https://prove2.me/theorems/0e88fe11-963e-55ef-a44d-8b86b321fc40
-- title:
--   I2: short vector bound le kappa
-- statement:
--   The I2 construction uses the short vector bound le kappa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ShortVectorBoundLeKappa.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ShortVectorBoundLeKappa.lean#L11-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofCovolLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ShortVectorBoundLeKappa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.short_vector_bound_le_kappa [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) :
    PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) ≤ P.ka0 * P.ph := by sorry
