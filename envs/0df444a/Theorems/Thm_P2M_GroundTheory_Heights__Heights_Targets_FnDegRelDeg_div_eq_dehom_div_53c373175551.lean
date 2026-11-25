-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_div_eq_dehom_div_53c373175551
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_div_eq_dehom_div_53c373175551
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:39.543554+00:00
-- url     : https://prove2.me/theorems/6c68f2e5-58b8-4b0a-8009-9ec14c2672ca
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg div eq dehom div 53c373175551: P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg div eq dehom div 53c373175551
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg div eq dehom div 53c373175551 construction uses the P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg div eq dehom div 53c373175551 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L81-L89

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

theorem P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_div_eq_dehom_div_53c373175551 (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) {b : K → ℕ} {f g : MRing ι F}
    (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) :
    algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V f) /
        algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V g) =
      IntNumPoint.dehom V i f / IntNumPoint.dehom V i g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FnDegRelDeg».«div_eq_dehom_div» := P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_div_eq_dehom_div_53c373175551
