-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameProj_basisFun_repr_3fd2d1412cc3
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameProj_basisFun_repr_3fd2d1412cc3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:21.616507+00:00
-- url     : https://prove2.me/theorems/ea9cfbeb-dc89-4a4c-91ed-aea5a7bd0da9
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Mass frame Proj basis Fun repr 3fd2d1412cc3: P2 M Ground Theory Heights  Heights Local Graph Mass frame Proj basis Fun repr 3fd2d1412cc3
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Mass frame Proj basis Fun repr 3fd2d1412cc3 construction uses the P2 M Ground Theory Heights  Heights Local Graph Mass frame Proj basis Fun repr 3fd2d1412cc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L29-L34

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

theorem P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameProj_basisFun_repr_3fd2d1412cc3 (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) :
    frameProj (EuclideanSpace.basisFun (Fin n) ℂ) I (b.repr z) = frameProj b I z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphMass».«frameProj_basisFun_repr» := P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameProj_basisFun_repr_3fd2d1412cc3
