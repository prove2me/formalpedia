-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_mul_eq_aeval_af68aaf6f222
-- name    : P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_mul_eq_aeval_af68aaf6f222
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:22.95379+00:00
-- url     : https://prove2.me/theorems/27d17544-c7bc-5e7e-a513-5f0879bd42a3
-- title:
--   P2 M Ground Theory Heights  Heights Hypersurface Presentation exists mul eq aeval af68aaf6f222: P2 M Ground Theory Heights  Heights Hypersurface Presentation exists mul eq aeval af68aaf6f222
-- statement:
--   The P2 M Ground Theory Heights  Heights Hypersurface Presentation exists mul eq aeval af68aaf6f222 construction uses the P2 M Ground Theory Heights  Heights Hypersurface Presentation exists mul eq aeval af68aaf6f222 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L52-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L52-L67

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
omit [CharZero E] [IsDomain A]

theorem P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_mul_eq_aeval_af68aaf6f222 {θ : A} (hθ : IsIntegral R θ)
    (hgen : IntermediateField.adjoin E {algebraMap A L θ} = ⊤) (x : A) :
    ∃ b : R, b ≠ 0 ∧ ∃ q : Polynomial R, Polynomial.aeval θ q = algebraMap R A b * x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HypersurfacePresentation».«exists_mul_eq_aeval» := P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_mul_eq_aeval_af68aaf6f222
