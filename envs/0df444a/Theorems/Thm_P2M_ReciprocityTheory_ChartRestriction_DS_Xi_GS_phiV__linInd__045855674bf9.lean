-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__linInd__045855674bf9
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__linInd__045855674bf9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:54.866248+00:00
-- url     : https://prove2.me/theorems/398d03f2-10ba-4ae1-b51d-671d92098458
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi GS phi V  lin Ind  045855674bf9: P2 M Reciprocity Theory Chart Restriction DS Xi GS phi V  lin Ind  045855674bf9
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi GS phi V  lin Ind  045855674bf9 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi GS phi V  lin Ind  045855674bf9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L34-L36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__linInd__045855674bf9 (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«GS».«phiV'_linInd'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__linInd__045855674bf9
