-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_Hf_smul_right
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_Hf_smul_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:30.942212+00:00
-- url     : https://prove2.me/theorems/8de9c673-32a5-4f58-8522-972ae1799167
-- title:
--   I2: n A Hf smul right
-- statement:
--   The I2 construction uses the n A Hf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L28-L32

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_Hf_smul_right (c : ℂ) (v w : EuclideanSpace ℂ ι) :
    Hf v (c • w) = (starRingEnd ℂ) c * Hf v w := by sorry
