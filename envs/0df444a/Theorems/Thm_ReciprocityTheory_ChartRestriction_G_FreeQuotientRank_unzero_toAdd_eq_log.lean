-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_unzero_toAdd_eq_log
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.unzero_toAdd_eq_log
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:48.835415+00:00
-- url     : https://prove2.me/theorems/8b19d382-ba7c-50b1-bda1-41ffd96d11d5
-- title:
--   Free Quotient Rank: unzero to Add eq log
-- statement:
--   The Free Quotient Rank construction uses the unzero to Add eq log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L10-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.unzero_toAdd_eq_log (y : WithZero (Multiplicative ℤ)) (hy : y ≠ 0) :
    (WithZero.unzero hy).toAdd = WithZero.log y := by sorry
