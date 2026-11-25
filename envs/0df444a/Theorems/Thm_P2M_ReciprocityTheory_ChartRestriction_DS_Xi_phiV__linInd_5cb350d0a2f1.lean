-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_phiV__linInd_5cb350d0a2f1
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_phiV__linInd_5cb350d0a2f1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:14:56.31861+00:00
-- url     : https://prove2.me/theorems/798e8c28-48e9-4e9b-9d9a-68e5d2755a72
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi phi V  lin Ind 5cb350d0a2f1: P2 M Reciprocity Theory Chart Restriction DS Xi phi V  lin Ind 5cb350d0a2f1
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi phi V  lin Ind 5cb350d0a2f1 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi phi V  lin Ind 5cb350d0a2f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L110-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L110-L110

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_phiV__linInd_5cb350d0a2f1 (k r : ℕ) (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«phiV'_linInd» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_phiV__linInd_5cb350d0a2f1
