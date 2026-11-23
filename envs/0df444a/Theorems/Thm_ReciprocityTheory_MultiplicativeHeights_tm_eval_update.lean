-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tm_eval_update
-- name    : ReciprocityTheory.MultiplicativeHeights.tm_eval_update
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:39.23922+00:00
-- url     : https://prove2.me/theorems/93c419ae-bc7b-4e95-8b6a-589708913acd
-- title:
--   Multiplicative Heights: tm eval update
-- statement:
--   The Multiplicative Heights construction uses the tm eval update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L89-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L89-L104

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.MultiplicativeHeights.tm_eval_update (i : ι) (x : ι → ℂ) (z : ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval (update x i z) f = (tmSlice i x f).eval z := by sorry
