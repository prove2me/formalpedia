-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_minpoly_separable_up_to_f836c61939fc
-- name    : P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_minpoly_separable_up_to_f836c61939fc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:44.743409+00:00
-- url     : https://prove2.me/theorems/88c424dd-8d69-4047-952b-dfbfb22f096c
-- title:
--   P2 M Ground Theory Heights  Heights Hypersurface Presentation minpoly separable up to f836c61939fc: P2 M Ground Theory Heights  Heights Hypersurface Presentation minpoly separable up to f836c61939fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Hypersurface Presentation minpoly separable up to f836c61939fc construction uses the P2 M Ground Theory Heights  Heights Hypersurface Presentation minpoly separable up to f836c61939fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L33-L48

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
omit [IsDomain A]
include E L

theorem P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_minpoly_separable_up_to_f836c61939fc [IsIntegrallyClosed R] {θ : A} (hθ : IsIntegral R θ) :
    ∃ δ : R, δ ≠ 0 ∧ ∃ u v : Polynomial R,
      u * minpoly R θ + v * Polynomial.derivative (minpoly R θ) = Polynomial.C δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HypersurfacePresentation».«minpoly_separable_up_to» := P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_minpoly_separable_up_to_f836c61939fc
