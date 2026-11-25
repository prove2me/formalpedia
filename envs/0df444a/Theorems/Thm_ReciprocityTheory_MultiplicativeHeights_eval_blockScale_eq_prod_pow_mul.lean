-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_blockScale_eq_prod_pow_mul
-- name    : ReciprocityTheory.MultiplicativeHeights.eval_blockScale_eq_prod_pow_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:00.966892+00:00
-- url     : https://prove2.me/theorems/45410858-2c38-5366-9f45-91f73c97b902
-- title:
--   Multiplicative Heights: eval block Scale eq prod pow mul
-- statement:
--   The Multiplicative Heights construction uses the eval block Scale eq prod pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L83-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L83-L96

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric

theorem ReciprocityTheory.MultiplicativeHeights.eval_blockScale_eq_prod_pow_mul {B n : ℕ} (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF : IsMultiHomogeneous a F) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    MvPolynomial.eval (fun p => r p.1 * x p) F = (∏ b, r b ^ a b) * MvPolynomial.eval x F := by sorry
