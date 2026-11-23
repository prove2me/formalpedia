-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coeffIn_eq_zero_of_lt
-- name    : ReciprocityTheory.MultiplicativeHeights.coeffIn_eq_zero_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:11.376163+00:00
-- url     : https://prove2.me/theorems/e2e976f4-1764-417a-837a-3962481b1894
-- title:
--   Multiplicative Heights: coeff In eq zero of lt
-- statement:
--   The Multiplicative Heights construction uses the coeff In eq zero of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanC.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanC.lean#L27-L33

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

theorem ReciprocityTheory.MultiplicativeHeights.coeffIn_eq_zero_of_lt (i : ι) (f : MvPolynomial ι ℂ) (k : ℕ)
    (hk : f.support.sup (fun s => s i) < k) : coeffIn i k f = 0 := by sorry
