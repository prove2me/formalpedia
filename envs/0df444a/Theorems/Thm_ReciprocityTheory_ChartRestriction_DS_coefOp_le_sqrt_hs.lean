-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefOp_le_sqrt_hs
-- name    : ReciprocityTheory.ChartRestriction.DS.coefOp_le_sqrt_hs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:36.812995+00:00
-- url     : https://prove2.me/theorems/c8ada2a5-b585-42c9-8053-477bc7546f08
-- title:
--   DS: coef Op le sqrt hs
-- statement:
--   The DS construction uses the coef Op le sqrt hs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CoefOp.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CoefOp.lean#L55-L59

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

theorem ReciprocityTheory.ChartRestriction.DS.coefOp_le_sqrt_hs (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ Real.sqrt (S7.hs A) := by sorry
