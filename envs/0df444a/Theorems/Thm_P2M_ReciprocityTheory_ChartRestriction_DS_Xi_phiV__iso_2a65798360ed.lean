-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_phiV__iso_2a65798360ed
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_phiV__iso_2a65798360ed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:14:04.127975+00:00
-- url     : https://prove2.me/theorems/9ce25018-b639-431e-bec9-b1cbaefc4f2a
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi phi V  iso 2a65798360ed: P2 M Reciprocity Theory Chart Restriction DS Xi phi V  iso 2a65798360ed
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi phi V  iso 2a65798360ed construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi phi V  iso 2a65798360ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L112-L113

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_phiV__iso_2a65798360ed (k r : ℕ) (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«phiV'_iso» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_phiV__iso_2a65798360ed
