-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_integral_primitive_79d7c8a66779
-- name    : P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_integral_primitive_79d7c8a66779
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:45.581635+00:00
-- url     : https://prove2.me/theorems/c36799b8-80dd-4983-847b-576ee1c7659b
-- title:
--   P2 M Ground Theory Heights  Heights Hypersurface Presentation exists integral primitive 79d7c8a66779: P2 M Ground Theory Heights  Heights Hypersurface Presentation exists integral primitive 79d7c8a667
-- statement:
--   The P2 M Ground Theory Heights  Heights Hypersurface Presentation exists integral primitive 79d7c8a66779 construction uses the P2 M Ground Theory Heights  Heights Hypersurface Presentation exists integral primitive 79d7c8a66779 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L71-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L71-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.HypersurfacePresentation
variable {R A E L : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Field E] [Algebra R E] [IsFractionRing R E] [CharZero E]
  [Field L] [Algebra A L] [IsFractionRing A L] [Algebra R L] [IsScalarTower R A L]
  [Algebra E L] [IsScalarTower R E L]
omit [IsDomain R] [IsDomain A]

theorem P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_integral_primitive_79d7c8a66779 [FaithfulSMul R A] [Algebra.IsAlgebraic R A] {n : ℕ} (x : Fin n → A)
    (hgen : IntermediateField.adjoin E (Set.range fun j => algebraMap A L (x j)) = ⊤) :
    ∃ θ : A, IsIntegral R θ ∧ IntermediateField.adjoin E {algebraMap A L θ} = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HypersurfacePresentation».«exists_integral_primitive» := P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_integral_primitive_79d7c8a66779
