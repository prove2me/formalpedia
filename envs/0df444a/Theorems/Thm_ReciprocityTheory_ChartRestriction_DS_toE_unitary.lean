-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_toE_unitary
-- name    : ReciprocityTheory.ChartRestriction.DS.toE_unitary
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:51.256528+00:00
-- url     : https://prove2.me/theorems/9147fe7b-ebe4-513f-9dbb-dd9ed1ed2d9a
-- title:
--   DS: to E unitary
-- statement:
--   The DS construction uses the to E unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L129-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L129-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.toE_unitary {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset (fun _ : Fin n => true))
    (v : EH n) : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℂ) g v‖ = ‖v‖ := by sorry
