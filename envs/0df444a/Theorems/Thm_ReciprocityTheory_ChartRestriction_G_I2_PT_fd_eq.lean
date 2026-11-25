-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_fd_eq
-- name    : ReciprocityTheory.ChartRestriction.G.I2.PT.fd_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:46.376267+00:00
-- url     : https://prove2.me/theorems/577370b8-7ca2-5da7-b6bc-a3398b34e8dc
-- title:
--   PT: fd eq
-- statement:
--   The PT construction uses the fd eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L49-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.PT.fd_eq (n : ℕ) : X.fd n = Set.univ.pi (fun _ : Fin n => ZSpan.fundamentalDomain X.b) := by sorry
