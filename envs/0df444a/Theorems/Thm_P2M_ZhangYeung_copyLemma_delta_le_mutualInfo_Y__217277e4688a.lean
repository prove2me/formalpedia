-- Prove2me | Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_Y__217277e4688a
-- name    : P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_Y__217277e4688a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:53:47.095794+00:00
-- url     : https://prove2.me/theorems/b55f0be5-96ff-48fe-8901-9f35016bf821
-- title:
--   P2 M Zhang Yeung copy Lemma delta le mutual Info Y  217277e4688a: P2 M Zhang Yeung copy Lemma delta le mutual Info Y  217277e4688a
-- statement:
--   **Primary inequality form of Lemma 2** [@zhangyeung1998, §III, eq. 45]. Combining
--   the Y-to-Y₁
--   delta transport with Form B and the nonnegativity of the three subtracted conditional
--   mutual
--   informations on the right of eq. (45) gives
--
--     `Δ(Z, U | X, Y) μ ≤ I[X' : Y₁; ν]`,
--
--   the first of the two inequalities Theorem 3's proof opens with on paper line 683.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L543-L560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L543-L560

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

theorem P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_Y__217277e4688a
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z U X Y μ ≤ I[X' : Y₁; ν] := by sorry

alias «ZhangYeung».«copyLemma_delta_le_mutualInfo_Y₁» := P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_Y__217277e4688a
