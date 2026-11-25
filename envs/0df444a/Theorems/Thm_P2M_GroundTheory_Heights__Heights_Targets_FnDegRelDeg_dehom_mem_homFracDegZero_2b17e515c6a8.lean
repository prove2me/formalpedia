-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_dehom_mem_homFracDegZero_2b17e515c6a8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_dehom_mem_homFracDegZero_2b17e515c6a8
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:33.918477+00:00
-- url     : https://prove2.me/theorems/692898f1-26f8-497a-be31-a25cc3b0cab3
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg dehom mem hom Frac Deg Zero 2b17e515c6a8: P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg dehom mem hom Frac Deg Zero 2b17e515c6a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg dehom mem hom Frac Deg Zero 2b17e515c6a8 construction uses the P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg dehom mem hom Frac Deg Zero 2b17e515c6a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L69-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_dehom_mem_homFracDegZero_2b17e515c6a8 (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) (f : MRing ι F) :
    IntNumPoint.dehom V i f ∈ homFracDegZero V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FnDegRelDeg».«dehom_mem_homFracDegZero» := P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_dehom_mem_homFracDegZero_2b17e515c6a8
