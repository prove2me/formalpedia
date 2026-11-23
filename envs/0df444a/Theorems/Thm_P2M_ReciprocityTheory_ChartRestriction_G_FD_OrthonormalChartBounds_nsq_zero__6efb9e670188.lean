-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_nsq_zero__6efb9e670188
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_nsq_zero__6efb9e670188
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:40.922012+00:00
-- url     : https://prove2.me/theorems/808fa505-7306-4368-8d1b-290dd0ff059f
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Chart Bounds nsq zero  6efb9e670188: P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Chart Bounds nsq zero  6efb9e670188
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Chart Bounds nsq zero  6efb9e670188 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Orthonormal Chart Bounds nsq zero  6efb9e670188 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L48-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_nsq_zero__6efb9e670188 {n : ℕ} : nsq (0 : Fin n → ℂ) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«OrthonormalChartBounds».«nsq_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_nsq_zero__6efb9e670188
