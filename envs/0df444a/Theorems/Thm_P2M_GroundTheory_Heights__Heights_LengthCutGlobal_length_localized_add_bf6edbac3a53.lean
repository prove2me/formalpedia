-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_add_bf6edbac3a53
-- name    : P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_add_bf6edbac3a53
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:25:58.504537+00:00
-- url     : https://prove2.me/theorems/a355501b-4e81-4eda-ac66-c5aab8d452cb
-- title:
--   P2 M Ground Theory Heights  Heights Length Cut Global length localized add bf6edbac3a53: P2 M Ground Theory Heights  Heights Length Cut Global length localized add bf6edbac3a53
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Cut Global length localized add bf6edbac3a53 construction uses the P2 M Ground Theory Heights  Heights Length Cut Global length localized add bf6edbac3a53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L17-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
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
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_add_bf6edbac3a53 {N M Q : Type*} [AddCommGroup N] [Module C N] [AddCommGroup M]
    [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl N) +
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthCutGlobal».«length_localized_add» := P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_add_bf6edbac3a53
