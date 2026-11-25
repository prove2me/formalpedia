-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_exists_div_of_mem_adjoin_ec9f4957fb2e
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_exists_div_of_mem_adjoin_ec9f4957fb2e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:28.03271+00:00
-- url     : https://prove2.me/theorems/128c3767-41f3-4416-bba3-05dc6b70e468
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg exists div of mem adjoin ec9f4957fb2e: P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg exists div of mem adjoin ec9f4957fb2e
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg exists div of mem adjoin ec9f4957fb2e construction uses the P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg exists div of mem adjoin ec9f4957fb2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L16-L25

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

theorem P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_exists_div_of_mem_adjoin_ec9f4957fb2e {F R L : Type*} [Field F] [CommRing R] [Field L] [Algebra F L]
    (τ : R →+* L) (hF : ∀ c : F, ∃ x, τ x = algebraMap F L c) {z : L}
    (hz : z ∈ IntermediateField.adjoin F (Set.range τ)) : ∃ x y, z = τ x / τ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FnDegRelDeg».«exists_div_of_mem_adjoin» := P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_exists_div_of_mem_adjoin_ec9f4957fb2e
