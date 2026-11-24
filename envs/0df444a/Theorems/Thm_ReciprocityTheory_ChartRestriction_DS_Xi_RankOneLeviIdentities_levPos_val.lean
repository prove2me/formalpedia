-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levPos_val
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.levPos_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:40:38.907255+00:00
-- url     : https://prove2.me/theorems/32ed2468-57a7-45d8-8789-b7b7943cdc06
-- title:
--   Rank One Levi Identities: lev Pos val
-- statement:
--   The Rank One Levi Identities construction uses the lev Pos val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L131-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L131-L131

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.levPos_val (j : Fin (2 * r' + k + 1)) : (levPos k 1 r' j).val = j.val + 1 := by sorry
