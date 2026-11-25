-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_Hf_self_im
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_Hf_self_im
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:57.238875+00:00
-- url     : https://prove2.me/theorems/81a913db-8f2e-5780-bef9-e51167995592
-- title:
--   I2: n A Hf self im
-- statement:
--   The I2 construction uses the n A Hf self im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L37-L41

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_Hf_self_im (v : EuclideanSpace ℂ ι) : (Hf v v).im = 0 := by sorry
