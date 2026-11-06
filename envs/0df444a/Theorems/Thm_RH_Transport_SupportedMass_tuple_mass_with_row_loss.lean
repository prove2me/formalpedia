-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_tuple_mass_with_row_loss
-- name    : RH.Transport.SupportedMass.tuple_mass_with_row_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:57:14.413193+00:00
-- url     : https://prove2.me/theorems/bb50dedc-1650-4af5-ae3b-fa0b76c6839e
-- title:
--   Supported Mass: tuple mass with row loss
-- statement:
--   Finite tuple mass with the specified half-row loss fully absorbed. A
--   subset of physical slots is represented by taking the index type to be that
--   finite subset. The theorem does not require a bound on the subset cardinality.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L188-L205
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L188-L205

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.tuple_mass_with_row_loss {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (q w : ∀ i, α i → ℝ) (a C ell : ι → ℝ) {p Z : ℝ}
    (hp : p < 1 / 30) (hZ : 1 ≤ Z)
    (ha : ∀ i, 0 < a i) (hC : ∀ i, 0 ≤ C i)
    (hell : ∀ i, 0 ≤ ell i)
    (hq : ∀ i j, 0 ≤ q i j) (hw : ∀ i j, 0 ≤ w i j)
    (hsupport : ∀ i j, w i j ≠ 0 → a i * Z ^ ell i ≤ q i j)
    (hmass : ∀ i, (∑ j, w i j * q i j ^ (-(3 / 2 : ℝ))) ≤ C i) :
    (∑ t : ∀ i, α i, ∏ i, w i (t i) * q i (t i) ^ (-2 : ℝ)) *
        Z ^ (max 0 (5 * Geometry.ell p - 1 + (∑ i, ell i)) / 8) ≤
      ∏ i, C i * a i ^ (-(1 / 2 : ℝ)) := by sorry
