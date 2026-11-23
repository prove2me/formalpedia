-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemSJ_det
-- name    : ReciprocityTheory.ChartRestriction.G.I2.lemSJ_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:17.68982+00:00
-- url     : https://prove2.me/theorems/de31c29c-b95d-4008-9e2a-6a0afa0a1cd2
-- title:
--   I2: lem SJ det
-- statement:
--   The I2 construction uses the lem SJ det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L29-L43

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

theorem ReciprocityTheory.ChartRestriction.G.I2.lemSJ_det : |LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _)| = 1 := by sorry
