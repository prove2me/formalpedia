-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefOp_unitary_le_one
-- name    : ReciprocityTheory.ChartRestriction.DS.coefOp_unitary_le_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:32.024828+00:00
-- url     : https://prove2.me/theorems/48677895-4848-5d32-97b2-c6c34003d901
-- title:
--   DS: coef Op unitary le one
-- statement:
--   The DS construction uses the coef Op unitary le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CoefOp.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CoefOp.lean#L45-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.coefOp_unitary_le_one {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) k‖ ≤ 1 := by sorry
