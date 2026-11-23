-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_latticeBoundAtMaximum_of_transference
-- name    : ReciprocityTheory.ChartRestriction.G.FD.latticeBoundAtMaximum_of_transference
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:50:35.624478+00:00
-- url     : https://prove2.me/theorems/4e44fb55-73e0-4f1f-94ee-1352a884e9b7
-- title:
--   FD: lattice Bound At Maximum of transference
-- statement:
--   The FD construction uses the lattice Bound At Maximum of transference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeBoundAtMaximumOfTransference.lean#L17-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeBoundAtMaximumOfTransference.lean#L17-L213

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SmallOperatorExistence
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeBoundAtMaximumOfTransference
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.latticeBoundAtMaximum_of_transference (hD5 : CoveringRadiusStatement) : LatticeBoundAtMaximum (E := E) := by sorry
