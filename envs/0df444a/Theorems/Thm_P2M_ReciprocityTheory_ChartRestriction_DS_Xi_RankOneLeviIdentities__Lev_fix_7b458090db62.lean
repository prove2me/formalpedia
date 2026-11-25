-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_fix_7b458090db62
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_fix_7b458090db62
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:44.165565+00:00
-- url     : https://prove2.me/theorems/99d63b5b-3b54-4662-8ac5-93e9c019f786
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities  Lev fix 7b458090db62: P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities  Lev fix 7b458090db62
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities  Lev fix 7b458090db62 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities  Lev fix 7b458090db62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L188-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L188-L197

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_fix_7b458090db62 (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hu : ∀ q : Fin (2 * (1 + r') + k + 1), (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) → u q = 0) :
    ιLev k 1 r' g *ᵥ u = u := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«RankOneLeviIdentities».«ιLev_fix» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_fix_7b458090db62
