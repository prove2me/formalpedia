-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_log_support_finite
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:46.133864+00:00
-- url     : https://prove2.me/theorems/08e855b4-fb41-426e-ac5f-64745f9d909d
-- title:
--   Multiplicative Heights: gauss abs log support finite
-- statement:
--   The Multiplicative Heights construction uses the gauss abs log support finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LagrangeIdealLiftsFact.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LagrangeIdealLiftsFact.lean#L8-L27

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory NumberField

theorem ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite {K : Type*} [Field K] [NumberField K] {σ : Type*}
    (f : MvPolynomial σ K) (hf : f ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (gaussAbs w f)).Finite := by sorry
