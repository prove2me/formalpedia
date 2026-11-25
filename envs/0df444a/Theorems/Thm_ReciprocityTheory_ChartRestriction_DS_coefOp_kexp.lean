-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefOp_kexp
-- name    : ReciprocityTheory.ChartRestriction.DS.coefOp_kexp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:26.687554+00:00
-- url     : https://prove2.me/theorems/62c2a35a-4477-405d-ab93-118802ee601f
-- title:
--   DS: coef Op kexp
-- statement:
--   The DS construction uses the coef Op kexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CoefOp.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CoefOp.lean#L83-L88

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

theorem ReciprocityTheory.ChartRestriction.DS.coefOp_kexp {ε : Fin n → Bool} (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toMK k * NormedSpace.exp X)‖ ≤ Real.exp (Real.sqrt (S7.hs X)) := by sorry
