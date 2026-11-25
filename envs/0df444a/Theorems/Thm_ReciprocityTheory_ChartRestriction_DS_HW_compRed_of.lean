-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_compRed_of
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.compRed_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:23.315869+00:00
-- url     : https://prove2.me/theorems/64f651c9-0d75-4be2-b68c-af70e689f73e
-- title:
--   HW: comp Red of
-- statement:
--   The HW construction uses the comp Red of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Decomp.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Decomp.lean#L31-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Decomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem ReciprocityTheory.ChartRestriction.DS.HW.compRed_of (hR : KRepRelStatement) (hS : KRepStableStatement) (hP : KRepPieceStatement) :
    CompRedStatement := by sorry
