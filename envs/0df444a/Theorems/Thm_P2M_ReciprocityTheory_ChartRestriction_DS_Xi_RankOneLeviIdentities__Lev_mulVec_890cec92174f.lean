-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_mulVec_890cec92174f
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_mulVec_890cec92174f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:01:15.474884+00:00
-- url     : https://prove2.me/theorems/4d3f71f7-31fb-40c2-a669-f5c5fde78f50
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities  Lev mul Vec 890cec92174f: P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities  Lev mul Vec 890cec92174f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities  Lev mul Vec 890cec92174f construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities  Lev mul Vec 890cec92174f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L158-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L158-L177

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_mulVec_890cec92174f (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) :
    (ιLev k 1 r' g *ᵥ u) p = if h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then
      (g *ᵥ fun j => u (levPos k 1 r' j)) ⟨p.val - 1, by omega⟩ else u p := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«RankOneLeviIdentities».«ιLev_mulVec» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_mulVec_890cec92174f
