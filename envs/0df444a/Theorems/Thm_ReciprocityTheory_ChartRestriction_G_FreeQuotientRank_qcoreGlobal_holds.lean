-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_qcoreGlobal_holds
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.qcoreGlobal_holds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:50.947626+00:00
-- url     : https://prove2.me/theorems/469eb59f-aa50-51cb-9bc8-9ce8c2358219
-- title:
--   Free Quotient Rank: qcore Global holds
-- statement:
--   The Free Quotient Rank construction uses the qcore Global holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L127-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L127-L207

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf
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
open scoped TensorProduct

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.qcoreGlobal_holds : QCoreGlobalStatement := by sorry
