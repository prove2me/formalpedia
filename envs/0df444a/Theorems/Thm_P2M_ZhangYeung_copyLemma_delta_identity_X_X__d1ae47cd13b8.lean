-- Prove2me | Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_identity_X_X__d1ae47cd13b8
-- name    : P2M_ZhangYeung_copyLemma_delta_identity_X_X__d1ae47cd13b8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:16.040654+00:00
-- url     : https://prove2.me/theorems/53cad664-bed2-47ce-900d-a460eedbc021
-- title:
--   P2 M Zhang Yeung copy Lemma delta identity X X  d1ae47cd13b8: P2 M Zhang Yeung copy Lemma delta identity X X  d1ae47cd13b8
-- statement:
--   **Lemma 2 Form B (symmetric)** [@zhangyeung1998, §III, eq. 45]. The delta identity
--   of Lemma 2
--   instantiated at the copy's `(X', X₁, Z', U')` projections, the `X ↔ X₁` swap of
--   `copyLemma_delta_identity_Y₁`:
--
--     `Δ(Z', U' | X', X₁) = I[X' : X₁] - I[X' : X₁ | Z'] - I[X' : X₁ | U'] - I[Z' : U' |
--     ⟨X', X₁⟩]`
--
--   under the copy measure `ν`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L442-L451
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L442-L451

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
omit [Finite S₂] [MeasurableSingletonClass S₂]

theorem P2M_ZhangYeung_copyLemma_delta_identity_X_X__d1ae47cd13b8
    (hX' : Measurable X') (hX₁ : Measurable X₁) (hZ' : Measurable Z') (hU' : Measurable U')
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z' U' X' X₁ ν
      = I[X' : X₁; ν] - I[X' : X₁ | Z'; ν] - I[X' : X₁ | U'; ν]
        - I[Z' : U' | ⟨X', X₁⟩; ν] := by sorry

alias «ZhangYeung».«copyLemma_delta_identity_X_X₁» := P2M_ZhangYeung_copyLemma_delta_identity_X_X__d1ae47cd13b8
