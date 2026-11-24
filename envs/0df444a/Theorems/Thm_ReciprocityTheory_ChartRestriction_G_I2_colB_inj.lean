-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_colB_inj
-- name    : ReciprocityTheory.ChartRestriction.G.I2.colB_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:31.711497+00:00
-- url     : https://prove2.me/theorems/79ef52f5-7c21-468d-8757-5b92d7dbf775
-- title:
--   I2: col B inj
-- statement:
--   The I2 construction uses the col B inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OwnerNoneIff.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OwnerNoneIff.lean#L16-L23

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

theorem ReciprocityTheory.ChartRestriction.G.I2.colB_inj (hD : Disj bs) : Function.Injective (colB bs) := by sorry
