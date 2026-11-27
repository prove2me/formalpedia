-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_self_ofReal
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_HC_self_ofReal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:32.463797+00:00
-- url     : https://prove2.me/theorems/714612fd-1090-49ca-80f4-23e0199c67d3
-- title:
--   I2: n A HC self of Real
-- statement:
--   The I2 construction uses the n A HC self of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L66-L67

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_HC_self_ofReal (v : Fin n → EuclideanSpace ℂ ι) : HC v v = ((HC v v).re : ℂ) := by sorry
