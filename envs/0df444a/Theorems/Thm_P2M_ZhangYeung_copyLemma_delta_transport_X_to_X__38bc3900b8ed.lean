-- Prove2me | Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_transport_X_to_X__38bc3900b8ed
-- name    : P2M_ZhangYeung_copyLemma_delta_transport_X_to_X__38bc3900b8ed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:15.676286+00:00
-- url     : https://prove2.me/theorems/3e8c1444-74de-4b05-a530-aa21a87a1a1b
-- title:
--   P2 M Zhang Yeung copy Lemma delta transport X to X  38bc3900b8ed: P2 M Zhang Yeung copy Lemma delta transport X to X  38bc3900b8ed
-- statement:
--   Symmetric bridge identity: `Δ(Z, U | X, X) μ = Δ(Z', U' | X', X₁) ν`. Transports both
--   conditional-MI terms via `copyLemma_triple_XFirst` and `copyLemma_triple_XSecond`. The
--   μ-side has
--   `X` in both conditioner slots, so the two transports target the same pattern
--   syntactically; closing
--   by `linarith` over the two transport equalities sidesteps the ambiguity `rw` would
--   otherwise face.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L515-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L515-L532

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

theorem P2M_ZhangYeung_copyLemma_delta_transport_X_to_X__38bc3900b8ed
    (hX : Measurable X) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    delta Z U X X μ = delta Z' U' X' X₁ ν := by sorry

alias «ZhangYeung».«copyLemma_delta_transport_X_to_X₁» := P2M_ZhangYeung_copyLemma_delta_transport_X_to_X__38bc3900b8ed
