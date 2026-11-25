-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_frameFibreCount_image_repr_map_e35b58a6ec96
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_frameFibreCount_image_repr_map_e35b58a6ec96
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:41.536741+00:00
-- url     : https://prove2.me/theorems/7db8a4b2-726f-4dfb-9e24-3062271c56d9
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Projection Mass frame Fibre Count image repr map e35b58a6ec96: P2 M Ground Theory Heights  Heights Local Graph Projection Mass frame Fibre Count image r
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Projection Mass frame Fibre Count image repr map e35b58a6ec96 construction uses the P2 M Ground Theory Heights  Heights Local Graph Projection Mass frame Fibre Count image repr map e35b58a6ec96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphProjectionMass.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphProjectionMass.lean#L19-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphProjectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphProjectionMass
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
open GroundTheory.Heights₂.Heights.LocalGraphProjectionMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_frameFibreCount_image_repr_map_e35b58a6ec96 (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (A : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) :
    frameFibreCount (c.map b.repr) I (b.repr '' A) x = frameFibreCount c I A x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphProjectionMass».«frameFibreCount_image_repr_map» := P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_frameFibreCount_image_repr_map_e35b58a6ec96
