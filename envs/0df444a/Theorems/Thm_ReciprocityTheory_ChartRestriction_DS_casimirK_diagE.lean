-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_diagE
-- name    : ReciprocityTheory.ChartRestriction.DS.casimirK_diagE
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:51:12.294502+00:00
-- url     : https://prove2.me/theorems/2ae7f5ea-e69e-5fb0-a446-f18cc953b368
-- title:
--   DS: casimir K diag E
-- statement:
--   The DS construction uses the casimir K diag E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqB.lean#L151-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqB.lean#L151-L160

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
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

theorem ReciprocityTheory.ChartRestriction.DS.casimirK_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) :
    casimirK ε (diagE ε E cp cm) =
      casimirK ε E + (2 : ℂ) • crossT ε E cp cm + casimirK ε (sgE ε cp cm) := by sorry
