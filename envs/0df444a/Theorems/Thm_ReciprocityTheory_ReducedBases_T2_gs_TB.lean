-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_TB
-- name    : ReciprocityTheory.ReducedBases.T2.gs_TB
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:59.447856+00:00
-- url     : https://prove2.me/theorems/f4c15fd7-671b-4652-8b71-3c0fa2b6aa53
-- title:
--   T2: gs TB
-- statement:
--   The T2 construction uses the gs TB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L172-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L172-L184

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}

theorem ReciprocityTheory.ReducedBases.T2.gs_TB (B : Matrix (Fin d) (Fin d) ℝ) {K : ℝ} (hK : ∀ v, ‖v‖ ≤ K * ‖TB B v‖)
    (U : Fin d → EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    ‖gs U j‖ ≤ K * ‖gs (fun i => TB B (U i)) j‖ := by sorry
