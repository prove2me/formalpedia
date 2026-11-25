-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_of_orthogonal_30fcb0026ad7
-- name    : P2M_GroundTheory_Heights__Heights_det_gram_sumElim_of_orthogonal_30fcb0026ad7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:42.99255+00:00
-- url     : https://prove2.me/theorems/99e2c694-da69-4be6-978f-dd8c33ccbb36
-- title:
--   P2 M Ground Theory Heights  Heights det gram sum Elim of orthogonal 30fcb0026ad7: P2 M Ground Theory Heights  Heights det gram sum Elim of orthogonal 30fcb0026ad7
-- statement:
--   The P2 M Ground Theory Heights  Heights det gram sum Elim of orthogonal 30fcb0026ad7 construction uses the P2 M Ground Theory Heights  Heights det gram sum Elim of orthogonal 30fcb0026ad7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L17-L26

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

theorem P2M_GroundTheory_Heights__Heights_det_gram_sumElim_of_orthogonal_30fcb0026ad7 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (v : ι → V) (w : κ → V) (h : ∀ i j, inner ℂ (v i) (w j) = 0) :
    det (gram ℂ (Sum.elim v w)) = det (gram ℂ v) * det (gram ℂ w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_gram_sumElim_of_orthogonal» := P2M_GroundTheory_Heights__Heights_det_gram_sumElim_of_orthogonal_30fcb0026ad7
