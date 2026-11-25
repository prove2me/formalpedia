-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_unipotent_majorant_bound_data
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_majorant_bound_data
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:45.603456+00:00
-- url     : https://prove2.me/theorems/d2553f68-475f-426b-be02-23bb22a92c0f
-- title:
--   Data: unipotent majorant bound data
-- statement:
--   The Data construction uses the unipotent majorant bound data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantBoundOrthogonalPart.lean#L70-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantBoundOrthogonalPart.lean#L70-L258

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantBoundOrthogonalPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_majorant_bound_data : ReducedFrameDomainCovering (E := E) := by sorry
