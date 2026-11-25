-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_eq_c804c0ba1527
-- name    : P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_eq_c804c0ba1527
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:09.848903+00:00
-- url     : https://prove2.me/theorems/20ec1489-faf5-41b4-8c40-81e7e933a4ab
-- title:
--   P2 M Ground Theory Heights  Heights Length Cut Global lengths eq c804c0ba1527: P2 M Ground Theory Heights  Heights Length Cut Global lengths eq c804c0ba1527
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Cut Global lengths eq c804c0ba1527 construction uses the P2 M Ground Theory Heights  Heights Length Cut Global lengths eq c804c0ba1527 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L154-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L154-L211

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

theorem P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_eq_c804c0ba1527 {C : Type u} [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (hPID : IsPrincipalIdealRing (C ⧸ P)) (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal)
    (k : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
      (∀ p ∈ P ^ k, ∀ m : M, p • m = 0) → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (QuotSMulTop y M) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthCutGlobal».«lengths_eq» := P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_eq_c804c0ba1527
