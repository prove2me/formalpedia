-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_rootDiscriminant_eq_rpow
-- name    : ReciprocityTheory.ChartRestriction.G.FD.rootDiscriminant_eq_rpow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:23.735326+00:00
-- url     : https://prove2.me/theorems/57042958-902f-5e92-9cef-11a12f8cb2c6
-- title:
--   FD: root Discriminant eq rpow
-- statement:
--   The FD construction uses the root Discriminant eq rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L31-L33

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

theorem ReciprocityTheory.ChartRestriction.G.FD.rootDiscriminant_eq_rpow : rdE E = dE E ^ (1 / (2 * (fdeg E : ℝ))) := by sorry
