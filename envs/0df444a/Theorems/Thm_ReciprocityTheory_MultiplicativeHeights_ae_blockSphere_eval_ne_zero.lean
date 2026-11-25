-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_blockSphere_eval_ne_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.ae_blockSphere_eval_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:46.478291+00:00
-- url     : https://prove2.me/theorems/d379f59e-df45-4b62-b23c-7b71c7405c49
-- title:
--   Multiplicative Heights: ae block Sphere eval ne zero
-- statement:
--   The Multiplicative Heights construction uses the ae block Sphere eval ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L219-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L219-L223

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

theorem ReciprocityTheory.MultiplicativeHeights.ae_blockSphere_eval_ne_zero (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(blockSphereProb B n), MvPolynomial.eval (blockPoint z) F ≠ 0 := by sorry
