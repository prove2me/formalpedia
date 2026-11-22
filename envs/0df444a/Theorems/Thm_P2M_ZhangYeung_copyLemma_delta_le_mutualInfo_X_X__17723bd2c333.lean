-- Prove2me | Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_X_X__17723bd2c333
-- name    : P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_X_X__17723bd2c333
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:53:51.803013+00:00
-- url     : https://prove2.me/theorems/e274c530-4b3d-409e-bd2c-a8d3682b38da
-- title:
--   P2 M Zhang Yeung copy Lemma delta le mutual Info X X  17723bd2c333: P2 M Zhang Yeung copy Lemma delta le mutual Info X X  17723bd2c333
-- statement:
--   **Symmetric inequality form of Lemma 2** [@zhangyeung1998, §III, eq. 45]. The `X ↔
--   X₁` variant,
--
--     `I[Z : U; μ] - 2·I[Z : U | X; μ] ≤ I[X' : X₁; ν]`,
--
--   the second of the two inequalities Theorem 3's proof opens with on paper line 689.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L569-L587
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L569-L587

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
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}
omit [Finite S₂] [MeasurableSingletonClass S₂]

theorem P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_X_X__17723bd2c333
    (hX : Measurable X) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    I[Z : U; μ] - 2 * I[Z : U | X; μ] ≤ I[X' : X₁; ν] := by sorry

alias «ZhangYeung».«copyLemma_delta_le_mutualInfo_X_X₁» := P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_X_X__17723bd2c333
