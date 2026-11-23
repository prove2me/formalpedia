-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_dedekindRank
-- name    : ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:10.481321+00:00
-- url     : https://prove2.me/theorems/7dce537a-92e6-477b-ab67-4e0e43e852b7
-- title:
--   Closed: dedekind Rank
-- statement:
--   The Closed construction uses the dedekind Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AlgAll.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AlgAll.lean#L19-L19

import Definitions.Def_ReciprocityTheory_SemistableReduction_FinrankRestrictTotalDegree
import Definitions.Def_ReciprocityTheory_SemistableReduction_RankEqualityHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_CauchyInequalityOnTorus
import Definitions.Def_ReciprocityTheory_SemistableReduction_GenericImageFinite
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussExtensionAndResidueTrdegEq
import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_DetSubtypeCompAssociatedProd
import Definitions.Def_ReciprocityTheory_SemistableReduction_NormValuationEqFactorization
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed
open ReciprocityTheory.MultiplicativeHeights

theorem ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank : DedekindRankStatement := by sorry
