-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_const_of_vars_empty
-- name    : ReciprocityTheory.MultiplicativeHeights.eval_const_of_vars_empty
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:10.705622+00:00
-- url     : https://prove2.me/theorems/ec93b2b0-b153-40e3-a264-7956782e48fc
-- title:
--   Multiplicative Heights: eval const of vars empty
-- statement:
--   The Multiplicative Heights construction uses the eval const of vars empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanC.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanC.lean#L65-L69

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
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

theorem ReciprocityTheory.MultiplicativeHeights.eval_const_of_vars_empty (f : MvPolynomial ι ℂ) (hf : f.vars ⊆ ∅) (x : ι → ℂ) :
    MvPolynomial.eval x f = MvPolynomial.constantCoeff f := by sorry
