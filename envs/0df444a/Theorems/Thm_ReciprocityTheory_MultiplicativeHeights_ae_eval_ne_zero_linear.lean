-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_eval_ne_zero_linear
-- name    : ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:27:42.786284+00:00
-- url     : https://prove2.me/theorems/af047cbd-d55f-4070-b6bb-d37855be42d0
-- title:
--   Multiplicative Heights: ae eval ne zero linear
-- statement:
--   The Multiplicative Heights construction uses the ae eval ne zero linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L55-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L55-L81

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

theorem ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] (L : V ≃ₗ[ℂ] (ι → ℂ))
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ x ∂μ, MvPolynomial.eval (L x) f ≠ 0 := by sorry
