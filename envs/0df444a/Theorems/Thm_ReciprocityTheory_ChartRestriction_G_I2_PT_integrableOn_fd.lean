-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_integrableOn_fd
-- name    : ReciprocityTheory.ChartRestriction.G.I2.PT.integrableOn_fd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:57.498472+00:00
-- url     : https://prove2.me/theorems/e331c6ad-2f62-4648-961b-b795d22bfba6
-- title:
--   PT: integrable On fd
-- statement:
--   The PT construction uses the integrable On fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContDiffOfDifferentiableFd.lean#L57-L60

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

theorem ReciprocityTheory.ChartRestriction.G.I2.PT.integrableOn_fd {n : ℕ} {g : (Fin n → Vsp X.dim) → ℂ} (hg : Continuous g) :
    IntegrableOn g (X.fd n) := by sorry
