-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_totalDegree_bind__le_e8e4d4bd1303
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_totalDegree_bind__le_e8e4d4bd1303
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:17.506304+00:00
-- url     : https://prove2.me/theorems/5dc2cd27-51a9-54a3-bcaa-2c511a7e3ee8
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW total Degree bind  le e8e4d4bd1303: P2 M Reciprocity Theory Chart Restriction DS HW total Degree bind  le e8e4d4bd1303
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW total Degree bind  le e8e4d4bd1303 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW total Degree bind  le e8e4d4bd1303 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelSpace.lean#L85-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelSpace.lean#L85-L100

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_totalDegree_bind__le_e8e4d4bd1303 {σ τ : Type*} (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial σ ℂ) : (MvPolynomial.bind₁ g Q).totalDegree ≤ Q.totalDegree := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«totalDegree_bind₁_le» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_totalDegree_bind__le_e8e4d4bd1303
