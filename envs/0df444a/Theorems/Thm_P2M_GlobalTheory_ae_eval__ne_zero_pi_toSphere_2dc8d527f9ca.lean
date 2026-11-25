-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ae_eval__ne_zero_pi_toSphere_2dc8d527f9ca
-- name    : P2M_GlobalTheory_ae_eval__ne_zero_pi_toSphere_2dc8d527f9ca
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:09.936054+00:00
-- url     : https://prove2.me/theorems/e5e463b5-ee13-4ee3-8167-3bbb317d60eb
-- title:
--   P2 M Global Theory ae eval  ne zero pi to Sphere 2dc8d527f9ca: P2 M Global Theory ae eval  ne zero pi to Sphere 2dc8d527f9ca
-- statement:
--   The P2 M Global Theory ae eval  ne zero pi to Sphere 2dc8d527f9ca construction uses the P2 M Global Theory ae eval  ne zero pi to Sphere 2dc8d527f9ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AeEvalCircleMapNeZero.lean#L75-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AeEvalCircleMapNeZero.lean#L75-L143

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralLogNormLeHalfLogIntegralSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AeEvalCircleMapNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct
open GlobalTheory

theorem P2M_GlobalTheory_ae_eval__ne_zero_pi_toSphere_2dc8d527f9ca (K : Type) [Field K] [Countable K] (sg : K →+* ℂ)
    (D N : ℕ) :
    ∀ᵐ t ∂(MeasureTheory.Measure.pi fun _ : Fin D =>
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere),
      ∀ p : MvPolynomial (Fin D × Fin (N + 1)) K, p ≠ 0 →
        MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p ≠ 0 := by sorry

alias «GlobalTheory».«ae_eval₂_ne_zero_pi_toSphere» := P2M_GlobalTheory_ae_eval__ne_zero_pi_toSphere_2dc8d527f9ca
