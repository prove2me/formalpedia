-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_owner_eq_none
-- name    : ReciprocityTheory.ChartRestriction.G.I2.owner_eq_none
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:33.018607+00:00
-- url     : https://prove2.me/theorems/be355375-2c23-5765-aa50-9fa63fbafc33
-- title:
--   I2: owner eq none
-- statement:
--   The I2 construction uses the owner eq none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OwnerNoneIff.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OwnerNoneIff.lean#L48-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivDeterminantPolyTensor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OwnerNoneIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)
variable {bs}
variable (bs)
variable {bs}

theorem ReciprocityTheory.ChartRestriction.G.I2.owner_eq_none {k : Fin n} (h : ∀ p, colB bs p ≠ k) : owner bs k = none := by sorry
