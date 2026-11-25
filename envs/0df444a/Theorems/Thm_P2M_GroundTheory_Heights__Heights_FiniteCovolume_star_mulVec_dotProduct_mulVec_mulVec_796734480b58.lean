-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_mulVec_dotProduct_mulVec_mulVec_796734480b58
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_mulVec_dotProduct_mulVec_mulVec_796734480b58
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:30.024259+00:00
-- url     : https://prove2.me/theorems/df4eeeec-0ca2-4c87-a393-25a9823c4ea1
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume star mul Vec dot Product mul Vec mul Vec 796734480b58: P2 M Ground Theory Heights  Heights Finite Covolume star mul Vec dot Product mul Vec mul Vec
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume star mul Vec dot Product mul Vec mul Vec 796734480b58 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume star mul Vec dot Product mul Vec mul Vec 796734480b58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchInvariant.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchInvariant.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_mulVec_dotProduct_mulVec_mulVec_796734480b58 (M H : Matrix ι ι ℂ) (y z : ι → ℂ) :
    star (M *ᵥ y) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star y ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«star_mulVec_dotProduct_mulVec_mulVec» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_mulVec_dotProduct_mulVec_mulVec_796734480b58
