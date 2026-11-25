-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_toSphere
-- name    : ReciprocityTheory.MultiplicativeHeights.ae_toSphere
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:11:39.953606+00:00
-- url     : https://prove2.me/theorems/8bc3d9e5-56c0-4860-ac1a-704804291b2f
-- title:
--   Multiplicative Heights: ae to Sphere
-- statement:
--   The Multiplicative Heights construction uses the ae to Sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L105-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L105-L208

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

theorem ReciprocityTheory.MultiplicativeHeights.ae_toSphere (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere),
      MvPolynomial.eval (blockPoint z) F ≠ 0 := by sorry
