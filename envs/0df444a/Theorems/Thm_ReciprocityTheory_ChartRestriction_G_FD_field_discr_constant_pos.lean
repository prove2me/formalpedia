-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_field_discr_constant_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.field_discr_constant_pos
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:38.498559+00:00
-- url     : https://prove2.me/theorems/ec3fcd6b-92d8-54d1-94f8-fbffd368e8e0
-- title:
--   FD: field discr constant pos
-- statement:
--   The FD construction uses the field discr constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L27-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.field_discr_constant_pos : 0 < dE E := by sorry
