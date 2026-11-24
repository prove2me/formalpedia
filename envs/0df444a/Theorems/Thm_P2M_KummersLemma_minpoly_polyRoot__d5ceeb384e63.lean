-- Prove2me | Theorems.Thm_P2M_KummersLemma_minpoly_polyRoot__d5ceeb384e63
-- name    : P2M_KummersLemma_minpoly_polyRoot__d5ceeb384e63
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:50.28299+00:00
-- url     : https://prove2.me/theorems/e9406a92-f292-48e8-8fe3-8a6b5425ce34
-- title:
--   P2 M Kummers Lemma minpoly poly Root  d5ceeb384e63: P2 M Kummers Lemma minpoly poly Root  d5ceeb384e63
-- statement:
--   The P2 M Kummers Lemma minpoly poly Root  d5ceeb384e63 construction uses the P2 M Kummers Lemma minpoly poly Root  d5ceeb384e63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/Field.lean#L200-L206
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/Field.lean#L200-L206

module
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field
set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField
attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
variable (u : (𝓞 K)ˣ)
  (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ p ≠ u)
open Polynomial IsCyclotomicExtension.Rat
open KummersLemma
variable [IsCyclotomicExtension {p} ℚ K]
include hu

theorem P2M_KummersLemma_minpoly_polyRoot__d5ceeb384e63 {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    minpoly (𝓞 K) (polyRoot hp hζ u hcong α e i : L) = (poly hp hζ u hcong) := by sorry

alias «KummersLemma».«minpoly_polyRoot'» := P2M_KummersLemma_minpoly_polyRoot__d5ceeb384e63
