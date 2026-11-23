-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tmSlice_coeff
-- name    : ReciprocityTheory.MultiplicativeHeights.tmSlice_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:55.357847+00:00
-- url     : https://prove2.me/theorems/b59d8020-ee88-4c69-8569-b8fe09d29286
-- title:
--   Multiplicative Heights: tm Slice coeff
-- statement:
--   The Multiplicative Heights construction uses the tm Slice coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L82-L87

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

theorem ReciprocityTheory.MultiplicativeHeights.tmSlice_coeff (i : ι) (x : ι → ℂ) (f : MvPolynomial ι ℂ) (k : ℕ) :
    (tmSlice i x f).coeff k = MvPolynomial.eval x (coeffIn i k f) := by sorry
