-- Prove2me | Theorems.Thm_SumProduct_volume_le_of_tsum_indicator_le
-- name    : SumProduct.volume_le_of_tsum_indicator_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:53.550796+00:00
-- url     : https://prove2.me/theorems/c7f70a3d-e9dd-4412-ad5b-5fe4614516a8
-- title:
--   Sum Product: volume le of tsum indicator le
-- statement:
--   **Blichfeldt integral inequality** (abstract). If every lattice translate of a measurable set
--   `S` is hit at most `N` times (`∑' ℓ, 𝟙_S(ℓ + y) ≤ N` for all `y`), then `vol S ≤ N · vol F` for a
--   fundamental domain `F` of the lattice `L`. This is the measure-theoretic core shared by the lower
--   bounds of Lemmas 3.5 and 3.7.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Blichfeldt.lean#L25-L42
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Blichfeldt.lean#L25-L42

import Mathlib
import Definitions.Def_SumProduct_Blichfeldt
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open MeasureTheory

theorem SumProduct.volume_le_of_tsum_indicator_le {E : Type*} [NormedAddCommGroup E] [MeasureSpace E]
    {L : Submodule ℤ E} [Countable ↥L] [MeasurableVAdd ↥L E] [VAddInvariantMeasure ↥L E volume]
    {F : Set E} (hF : IsAddFundamentalDomain (↥L) F volume) {S : Set E} (hSmeas : MeasurableSet S)
    {N : ℕ} (hbound : ∀ y : E,
      ∑' l : ↥L, S.indicator (fun _ => (1 : ENNReal)) (l +ᵥ y) ≤ (N : ENNReal)) :
    volume S ≤ (N : ENNReal) * volume F := by sorry
