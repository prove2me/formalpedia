-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_mem_of_forall_e89ec8f2dfbd
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_mem_of_forall_e89ec8f2dfbd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:26.173963+00:00
-- url     : https://prove2.me/theorems/a8836ce0-dcd8-43e5-b8f6-53b8015168f4
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Small aeval mem of forall e89ec8f2dfbd: P2 M Ground Theory Heights  Heights YPlus Small aeval mem of forall e89ec8f2dfbd
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Small aeval mem of forall e89ec8f2dfbd construction uses the P2 M Ground Theory Heights  Heights YPlus Small aeval mem of forall e89ec8f2dfbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L61-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_mem_of_forall_e89ec8f2dfbd {σ : Type*} {Ω : Type*} [CommRing Ω] (S : Subalgebra ℤ Ω) (w : σ → Ω)
    (hw : ∀ p, w p ∈ S) (F : MvPolynomial σ ℤ) : aeval w F ∈ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSmall».«aeval_mem_of_forall» := P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_mem_of_forall_e89ec8f2dfbd
