-- Prove2me | Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_identity_Y__c9ae01529d93
-- name    : P2M_ZhangYeung_copyLemma_delta_identity_Y__c9ae01529d93
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:57.985318+00:00
-- url     : https://prove2.me/theorems/ee247854-566a-4def-bca0-7d492b8f9422
-- title:
--   P2 M Zhang Yeung copy Lemma delta identity Y  c9ae01529d93: P2 M Zhang Yeung copy Lemma delta identity Y  c9ae01529d93
-- statement:
--   **Lemma 2 Form B (primary)** [@zhangyeung1998, §III, eq. 45]. The delta identity of
--   Lemma 2
--   instantiated at the copy's `(X', Y₁, Z', U')` projections:
--
--     `Δ(Z', U' | X', Y₁) = I[X' : Y₁] - I[X' : Y₁ | Z'] - I[X' : Y₁ | U'] - I[Z' : U' |
--     ⟨X', Y₁⟩]`
--
--   under the copy measure `ν`. The vanishing-CMI hypothesis is derived from the main
--   `CondIndepFun` by
--   projecting each measured pair to one coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L420-L430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L420-L430

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
variable {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}

theorem P2M_ZhangYeung_copyLemma_delta_identity_Y__c9ae01529d93
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z' U' X' Y₁ ν
      = I[X' : Y₁; ν] - I[X' : Y₁ | Z'; ν] - I[X' : Y₁ | U'; ν]
        - I[Z' : U' | ⟨X', Y₁⟩; ν] := by sorry

alias «ZhangYeung».«copyLemma_delta_identity_Y₁» := P2M_ZhangYeung_copyLemma_delta_identity_Y__c9ae01529d93
