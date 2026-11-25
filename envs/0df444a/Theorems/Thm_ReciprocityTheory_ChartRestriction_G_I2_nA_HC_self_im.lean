-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_self_im
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_HC_self_im
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:50.560019+00:00
-- url     : https://prove2.me/theorems/eae33a8e-56d0-4e9a-82f3-2e017a28d520
-- title:
--   I2: n A HC self im
-- statement:
--   The I2 construction uses the n A HC self im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L60-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {ι : Type} [Fintype ι]
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_HC_self_im (v : Fin n → EuclideanSpace ℂ ι) : (HC v v).im = 0 := by sorry
