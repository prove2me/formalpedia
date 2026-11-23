-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_conj
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Hf_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:39.071226+00:00
-- url     : https://prove2.me/theorems/c32acfbc-b2a6-4dcf-ab94-acafa640765f
-- title:
--   I2: Hf conj
-- statement:
--   The I2 construction uses the Hf conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L22-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
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
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.Hf_conj (v w : EuclideanSpace ℂ ι) : Hf w v = (starRingEnd ℂ) (Hf v w) := by sorry
