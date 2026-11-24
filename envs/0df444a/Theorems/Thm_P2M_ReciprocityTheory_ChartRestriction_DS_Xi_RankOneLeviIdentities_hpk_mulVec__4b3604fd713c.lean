-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_mulVec__4b3604fd713c
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_mulVec__4b3604fd713c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:17.885797+00:00
-- url     : https://prove2.me/theorems/f68e22e2-88b6-4c7f-95e2-caefdfdf15d4
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities hpk mul Vec  4b3604fd713c: P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities hpk mul Vec  4b3604fd713c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities hpk mul Vec  4b3604fd713c construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities hpk mul Vec  4b3604fd713c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L27-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L27-L43

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_mulVec__4b3604fd713c (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«RankOneLeviIdentities».«hpk_mulVec'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_mulVec__4b3604fd713c
