-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_unique_1911557ddd21
-- name    : P2M_GroundTheory_Heights__Heights_det_gram_unique_1911557ddd21
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:58.063872+00:00
-- url     : https://prove2.me/theorems/170bd2a6-8a7d-4b67-9100-b9536c944b71
-- title:
--   P2 M Ground Theory Heights  Heights det gram unique 1911557ddd21: P2 M Ground Theory Heights  Heights det gram unique 1911557ddd21
-- statement:
--   The P2 M Ground Theory Heights  Heights det gram unique 1911557ddd21 construction uses the P2 M Ground Theory Heights  Heights det gram unique 1911557ddd21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L70-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_GroundTheory_Heights__Heights_det_gram_unique_1911557ddd21 {κ : Type*} [Unique κ] (w : κ → V) :
    det (gram ℂ w) = ((‖w default‖ ^ 2 : ℝ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_gram_unique» := P2M_GroundTheory_Heights__Heights_det_gram_unique_1911557ddd21
