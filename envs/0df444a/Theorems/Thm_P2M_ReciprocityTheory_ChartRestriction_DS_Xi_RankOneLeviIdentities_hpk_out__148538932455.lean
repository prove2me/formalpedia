-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_out__148538932455
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_out__148538932455
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:14:08.21292+00:00
-- url     : https://prove2.me/theorems/44e63a18-0173-5430-a2d0-6a50cbe3532d
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities hpk out  148538932455: P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities hpk out  148538932455
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities hpk out  148538932455 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities hpk out  148538932455 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L15-L19

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
variable (k r : ℕ)

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_out__148538932455 {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«RankOneLeviIdentities».«hpk_out'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_out__148538932455
