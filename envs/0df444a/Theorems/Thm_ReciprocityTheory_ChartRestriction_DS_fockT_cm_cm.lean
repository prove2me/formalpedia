-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockT_cm_cm
-- name    : ReciprocityTheory.ChartRestriction.DS.fockT_cm_cm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:44.784373+00:00
-- url     : https://prove2.me/theorems/8550d6d8-24b9-52d9-be8c-99cb1ca4b837
-- title:
--   DS: fock T cm cm
-- statement:
--   The DS construction uses the fock T cm cm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L26-L30

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

theorem ReciprocityTheory.ChartRestriction.DS.fockT_cm_cm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (j b w z : Fin n) (y : W) :
    cm j b (cm w z y) = -(cm w z (cm j b y)) := by sorry
