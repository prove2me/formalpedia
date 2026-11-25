-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_genIndex_rep_cfb115622f69
-- name    : P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_genIndex_rep_cfb115622f69
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:59.936151+00:00
-- url     : https://prove2.me/theorems/44149b04-44e9-5d7d-a1df-144feeb5a935
-- title:
--   P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative gen Index rep cfb115622f69: P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative gen Index rep cfb115
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative gen Index rep cfb115622f69 construction uses the P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative gen Index rep cfb115622f69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L58-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L58-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_genIndex_rep_cfb115622f69 [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {X : AddSubgroup Ω} {β δ : B}
    {I : Ideal B} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hI : I ≠ ⊥)
    (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) :
    genIndex X B.toAddSubgroup = ((B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup : ℝ) /
      (((B.toAddSubgroup.map (mulBy (δ : Ω))).relIndex B.toAddSubgroup : ℝ) * (I.toAddSubgroup.index : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«InvertibleIndexMultiplicative».«genIndex_rep» := P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_genIndex_rep_cfb115622f69
