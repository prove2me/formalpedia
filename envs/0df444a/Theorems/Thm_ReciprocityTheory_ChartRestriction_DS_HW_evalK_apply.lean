-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_evalK_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.evalK_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:01:46.244797+00:00
-- url     : https://prove2.me/theorems/04f0de5e-8582-4393-9743-7517a5d6d588
-- title:
--   HW: eval K apply
-- statement:
--   The HW construction uses the eval K apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelSpace.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelSpace.lean#L55-L62

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.evalK_apply (ε : Fin n → Bool) (Q : MvPolynomial (Fin n × Fin n) ℂ) (x : KG ε) :
    evalK ε Q x = MvPolynomial.aeval (fun p : Fin n × Fin n => toMK x p.1 p.2) Q := by sorry
