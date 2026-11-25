-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockT_cm_cp
-- name    : ReciprocityTheory.ChartRestriction.DS.fockT_cm_cp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:13.906505+00:00
-- url     : https://prove2.me/theorems/a5e13beb-33e3-570f-8e8a-99814941635c
-- title:
--   DS: fock T cm cp
-- statement:
--   The DS construction uses the fock T cm cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L14-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.fockT_cm_cp {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) {ε : Fin n → Bool}
    {j b u v : Fin n} (hjb : ¬(ε j = true ∧ ε b = false)) (huv : ε u = true ∧ ε v = false) (y : W) :
    cm j b (cp u v y) = -(cp u v (cm j b y)) := by sorry
