-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_tuple_mass_decay
-- name    : RH.Transport.SupportedMass.tuple_mass_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:48.235385+00:00
-- url     : https://prove2.me/theorems/275f0c0d-aa7d-4ca1-947b-93792c369308
-- title:
--   Supported Mass: tuple mass decay
-- statement:
--   Product of supported masses, expressed as a sum over actual finite tuples.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L139-L157
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L139-L157

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.tuple_mass_decay {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (q w : ∀ i, α i → ℝ) (a C ell : ι → ℝ) {Z : ℝ}
    (hZ : 0 < Z) (ha : ∀ i, 0 < a i)
    (hq : ∀ i j, 0 ≤ q i j) (hw : ∀ i j, 0 ≤ w i j)
    (hsupport : ∀ i j, w i j ≠ 0 → a i * Z ^ ell i ≤ q i j)
    (hmass : ∀ i, (∑ j, w i j * q i j ^ (-(3 / 2 : ℝ))) ≤ C i) :
    (∑ t : ∀ i, α i, ∏ i, w i (t i) * q i (t i) ^ (-2 : ℝ)) ≤
      (∏ i, C i * a i ^ (-(1 / 2 : ℝ))) *
        Z ^ (-(∑ i, ell i) / 2) := by sorry
