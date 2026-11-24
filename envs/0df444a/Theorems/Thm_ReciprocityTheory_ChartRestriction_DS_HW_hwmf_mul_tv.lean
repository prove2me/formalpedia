-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_mul_tv
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.hwmf_mul_tv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:32:18.108802+00:00
-- url     : https://prove2.me/theorems/d51a5877-446d-47a6-97f4-a1a54bcbbe20
-- title:
--   HW: hwmf mul tv
-- statement:
--   The HW construction uses the hwmf mul tv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L192-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L192-L202

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.hwmf_mul_tv (x : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (s : ℂ) (r q : Fin n) :
    (x * (1 + s • single a b (1 : ℂ))) r q = x r q + (if q = b then s * x r a else 0) := by sorry
