-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_curve
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.KType.op_curve
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:19.464289+00:00
-- url     : https://prove2.me/theorems/ca0c3ec1-da7e-4210-831e-a11152518787
-- title:
--   KType: op curve
-- statement:
--   The KType construction uses the op curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/OneParam.lean#L84-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/OneParam.lean#L84-L142

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.KType.op_curve {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    T.op (γ t) = NormedSpace.exp ((t : ℂ) • T.dτ X) := by sorry
