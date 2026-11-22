-- Prove2me | Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_transport_Y_to_Y__4293faf356ee
-- name    : P2M_ZhangYeung_copyLemma_delta_transport_Y_to_Y__4293faf356ee
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:12.360077+00:00
-- url     : https://prove2.me/theorems/ca76b606-269a-453a-92bb-3e0536dc5dbb
-- title:
--   P2 M Zhang Yeung copy Lemma delta transport Y to Y  4293faf356ee: P2 M Zhang Yeung copy Lemma delta transport Y to Y  4293faf356ee
-- statement:
--   Bridge identity: `Δ(Z, U | X, Y) μ = Δ(Z', U' | X', Y₁) ν`. Each side of the delta
--   expands into
--   three mutual-information terms. `IdentDistrib.mutualInfo_eq` transports the
--   unconditional `I[Z :
--   U]`; `IdentDistrib.condMutualInfo_eq` transports the two conditional terms via the
--   triple-level
--   `IdentDistrib`s extracted from `hFirst` and `hSecond`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L490-L503
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L490-L503

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

theorem P2M_ZhangYeung_copyLemma_delta_transport_Y_to_Y__4293faf356ee
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    delta Z U X Y μ = delta Z' U' X' Y₁ ν := by sorry

alias «ZhangYeung».«copyLemma_delta_transport_Y_to_Y₁» := P2M_ZhangYeung_copyLemma_delta_transport_Y_to_Y__4293faf356ee
