-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_clear_denominators_86f7b5988c96
-- name    : P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_clear_denominators_86f7b5988c96
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:10.174801+00:00
-- url     : https://prove2.me/theorems/a8ce8a30-f09f-420d-955b-939003661c94
-- title:
--   P2 M Ground Theory Heights  Heights Hypersurface Presentation exists clear denominators 86f7b5988c96: P2 M Ground Theory Heights  Heights Hypersurface Presentation exists clear denominators 86f7b5988c
-- statement:
--   The P2 M Ground Theory Heights  Heights Hypersurface Presentation exists clear denominators 86f7b5988c96 construction uses the P2 M Ground Theory Heights  Heights Hypersurface Presentation exists clear denominators 86f7b5988c96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L24-L28

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

theorem P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_clear_denominators_86f7b5988c96 (p : Polynomial E) :
    ∃ b : R, b ≠ 0 ∧ ∃ p' : Polynomial R,
      p'.map (algebraMap R E) = Polynomial.C (algebraMap R E b) * p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HypersurfacePresentation».«exists_clear_denominators» := P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_clear_denominators_86f7b5988c96
