-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_algebraMap_0efebcebffdb
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_algebraMap_0efebcebffdb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:41:17.11416+00:00
-- url     : https://prove2.me/theorems/570ded5f-0548-4858-beff-b1b679525938
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg contract Frac Map algebra Map 0efebcebffdb: P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg contract Frac Map algebra Map 0efebceb
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg contract Frac Map algebra Map 0efebcebffdb construction uses the P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg contract Frac Map algebra Map 0efebcebffdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L98-L103

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

theorem P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_algebraMap_0efebcebffdb (f : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) =
      algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FnDegRelDeg».«contractFracMap_algebraMap» := P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_algebraMap_0efebcebffdb
