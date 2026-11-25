-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_comp_dehom_643f296b3106
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_comp_dehom_643f296b3106
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:31.565997+00:00
-- url     : https://prove2.me/theorems/108cfbb0-e034-4681-a395-902221c864fc
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg contract Frac Map comp dehom 643f296b3106: P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg contract Frac Map comp dehom 643f296b31
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg contract Frac Map comp dehom 643f296b3106 construction uses the P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg contract Frac Map comp dehom 643f296b3106 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L105-L111

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
variable {F : Type u} [Field F] {K K' : Type} {ι' : K' → Type} (j : K ↪ K') (P' : Ideal (MRing ι' F))
  [P'.IsPrime] (i' : ∀ k', ι' k')

theorem P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_comp_dehom_643f296b3106 :
    (contractFracMap j P').comp (IntNumPoint.dehom (contractPrime j P') (fun k => i' (j k))) =
      (IntNumPoint.dehom P' i').comp (rename (blockIncl j ι')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FnDegRelDeg».«contractFracMap_comp_dehom» := P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_comp_dehom_643f296b3106
