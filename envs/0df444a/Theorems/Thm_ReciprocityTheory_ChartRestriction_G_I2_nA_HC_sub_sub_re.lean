-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_sub_re
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_HC_sub_sub_re
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:20.320551+00:00
-- url     : https://prove2.me/theorems/48b46682-3c54-4bfe-b119-21a645154fc1
-- title:
--   I2: n A HC sub sub re
-- statement:
--   The I2 construction uses the n A HC sub sub re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L69-L73

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_HC_sub_sub_re (v a : Fin n → EuclideanSpace ℂ ι) :
    (HC (v - a) (v - a)).re = (HC v v).re - 2 * (HC v a).re + (HC a a).re := by sorry
