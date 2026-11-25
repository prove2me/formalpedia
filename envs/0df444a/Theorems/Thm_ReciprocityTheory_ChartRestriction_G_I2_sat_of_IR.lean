-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sat_of_IR
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sat_of_IR
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:59.159852+00:00
-- url     : https://prove2.me/theorems/2a87e806-a4a3-48ce-801a-eb2be5ccf558
-- title:
--   I2: sat of IR
-- statement:
--   The I2 construction uses the sat of IR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitC.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitC.lean#L54-L63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsMaximal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
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
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.sat_of_IR {X : PT E} {I : Submodule ℤ (Vsp X.dim)} (hs : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) :
    ∀ x ∈ X.L, ∀ k : ℤ, k ≠ 0 → k • x ∈ I → x ∈ I := by sorry
