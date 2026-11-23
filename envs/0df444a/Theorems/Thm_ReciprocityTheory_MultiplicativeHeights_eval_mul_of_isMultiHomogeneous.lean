-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_mul_of_isMultiHomogeneous
-- name    : ReciprocityTheory.MultiplicativeHeights.eval_mul_of_isMultiHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:00.63187+00:00
-- url     : https://prove2.me/theorems/14ce5ba1-591d-4aeb-b4fe-87c04816c4e6
-- title:
--   Multiplicative Heights: eval mul of is Multi Homogeneous
-- statement:
--   The Multiplicative Heights construction uses the eval mul of is Multi Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AevalIsWeightedHomogeneous.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AevalIsWeightedHomogeneous.lean#L29-L39

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
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
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.eval_mul_of_isMultiHomogeneous {B n : ℕ} {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (c : ℂ) (z : Fin B × Fin n → ℂ) :
    eval (fun p => c * z p) g = c ^ (∑ b, a b) * eval z g := by sorry
