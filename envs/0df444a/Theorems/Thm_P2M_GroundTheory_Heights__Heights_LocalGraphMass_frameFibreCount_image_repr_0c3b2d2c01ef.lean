-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_image_repr_0c3b2d2c01ef
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_image_repr_0c3b2d2c01ef
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:15.797024+00:00
-- url     : https://prove2.me/theorems/7e510b42-9f8b-557a-aeb1-ebfeb8f26409
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Mass frame Fibre Count image repr 0c3b2d2c01ef: P2 M Ground Theory Heights  Heights Local Graph Mass frame Fibre Count image repr 0c3b2d2c01ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Mass frame Fibre Count image repr 0c3b2d2c01ef construction uses the P2 M Ground Theory Heights  Heights Local Graph Mass frame Fibre Count image repr 0c3b2d2c01ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L36-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L36-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
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
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_image_repr_0c3b2d2c01ef (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (A : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) :
    frameFibreCount (EuclideanSpace.basisFun (Fin n) ℂ) I (b.repr '' A) x =
      frameFibreCount b I A x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphMass».«frameFibreCount_image_repr» := P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_image_repr_0c3b2d2c01ef
