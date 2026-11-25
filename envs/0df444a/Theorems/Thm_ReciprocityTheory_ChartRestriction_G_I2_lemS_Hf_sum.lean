-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_Hf_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.lemS_Hf_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:28:54.906596+00:00
-- url     : https://prove2.me/theorems/ca1db162-e472-4b3a-8ae8-bae468c51780
-- title:
--   I2: lem S Hf sum
-- statement:
--   The I2 construction uses the lem S Hf sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L45-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.lemS_Hf_sum {n : ℕ} (c : Fin n → ℤ) (v : Fin n → EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ ι) :
    (Hf (∑ i, c i • v i) y).im = ∑ i, (c i : ℝ) * (Hf (v i) y).im := by sorry
