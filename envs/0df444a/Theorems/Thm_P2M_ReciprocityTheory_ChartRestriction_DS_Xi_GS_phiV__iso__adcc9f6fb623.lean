-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__iso__adcc9f6fb623
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__iso__adcc9f6fb623
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:33.572812+00:00
-- url     : https://prove2.me/theorems/037f70a5-e66a-4b74-86dd-2ae02a4f44ce
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi GS phi V  iso  adcc9f6fb623: P2 M Reciprocity Theory Chart Restriction DS Xi GS phi V  iso  adcc9f6fb623
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi GS phi V  iso  adcc9f6fb623 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi GS phi V  iso  adcc9f6fb623 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L38-L39

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__iso__adcc9f6fb623 (hk : 1 ≤ k) (a b : Fin (r + 1)) : herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«GS».«phiV'_iso'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__iso__adcc9f6fb623
