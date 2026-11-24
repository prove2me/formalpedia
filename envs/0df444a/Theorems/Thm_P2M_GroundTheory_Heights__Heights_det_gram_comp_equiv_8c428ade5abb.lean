-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_comp_equiv_8c428ade5abb
-- name    : P2M_GroundTheory_Heights__Heights_det_gram_comp_equiv_8c428ade5abb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:12.204817+00:00
-- url     : https://prove2.me/theorems/bff54ce0-e14d-4459-a363-a290e4f1212a
-- title:
--   P2 M Ground Theory Heights  Heights det gram comp equiv 8c428ade5abb: P2 M Ground Theory Heights  Heights det gram comp equiv 8c428ade5abb
-- statement:
--   The P2 M Ground Theory Heights  Heights det gram comp equiv 8c428ade5abb construction uses the P2 M Ground Theory Heights  Heights det gram comp equiv 8c428ade5abb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L88-L91

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

theorem P2M_GroundTheory_Heights__Heights_det_gram_comp_equiv_8c428ade5abb {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (w : ι → V) : det (gram ℂ (w ∘ e)) = det (gram ℂ w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_gram_comp_equiv» := P2M_GroundTheory_Heights__Heights_det_gram_comp_equiv_8c428ade5abb
