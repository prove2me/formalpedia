-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_sub_a3ffef1fbd7a
-- name    : P2M_GroundTheory_Heights__Heights_det_gram_sumElim_sub_a3ffef1fbd7a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:42.006187+00:00
-- url     : https://prove2.me/theorems/335838fb-7b7a-4f2a-87fa-b216a36ca709
-- title:
--   P2 M Ground Theory Heights  Heights det gram sum Elim sub a3ffef1fbd7a: P2 M Ground Theory Heights  Heights det gram sum Elim sub a3ffef1fbd7a
-- statement:
--   The P2 M Ground Theory Heights  Heights det gram sum Elim sub a3ffef1fbd7a construction uses the P2 M Ground Theory Heights  Heights det gram sum Elim sub a3ffef1fbd7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L28-L40

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

theorem P2M_GroundTheory_Heights__Heights_det_gram_sumElim_sub_a3ffef1fbd7a {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → V) (u : κ → V) (M : Matrix ι κ ℂ) :
    det (gram ℂ (Sum.elim v (fun j ↦ u j - ∑ i, M i j • v i))) = det (gram ℂ (Sum.elim v u)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_gram_sumElim_sub» := P2M_GroundTheory_Heights__Heights_det_gram_sumElim_sub_a3ffef1fbd7a
