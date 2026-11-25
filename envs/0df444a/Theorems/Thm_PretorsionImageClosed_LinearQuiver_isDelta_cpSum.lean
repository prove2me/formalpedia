-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_isDelta_cpSum
-- name    : PretorsionImageClosed.LinearQuiver.isDelta_cpSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:47:03.83815+00:00
-- url     : https://prove2.me/theorems/efecd0ae-e5bb-54df-9789-8d1d9d4dd10e
-- title:
--   Linear Quiver: is Delta cp Sum
-- statement:
--   Lemma 7.3, equation (7.6): `cpSum (n + 1) = Δ_q(x² cpSum n)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L515-L523
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L515-L523

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.isDelta_cpSum (n : ℕ) : IsDelta (X ^ 2 * cpSum n) (cpSum (n + 1)) := by sorry
