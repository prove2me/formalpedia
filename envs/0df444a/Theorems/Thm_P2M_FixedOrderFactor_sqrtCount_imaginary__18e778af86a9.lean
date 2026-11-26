-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_imaginary__18e778af86a9
-- name    : P2M_FixedOrderFactor_sqrtCount_imaginary__18e778af86a9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:09.730809+00:00
-- url     : https://prove2.me/theorems/1589baf1-7ef8-42ac-9a02-408267d06fef
-- title:
--   P2 M Fixed Order Factor sqrt Count imaginary  18e778af86a9: P2 M Fixed Order Factor sqrt Count imaginary  18e778af86a9
-- statement:
--   **Imaginary families.** Let `r` be even, `M = 2r` and `a = 1 + r`. If `8 ∤ r` then
--   `β(2r, 1 + r, s) = 0` for every `s`. In general `β(2r, 1 + r, r/d) = 0` whenever `d ∣ r` is odd,
--   that is, the bias can be nonzero only for `b` whose exponent `d(b)` is even.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L245-L290
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L245-L290

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor

theorem P2M_FixedOrderFactor_sqrtCount_imaginary__18e778af86a9 {r : ℕ} (hr : 0 < r) (hev : Even r) :
    (¬ 8 ∣ r → ∀ s, sqrtCount (2 * r) (1 + r) s = 0) ∧
      (∀ d, d ∣ r → ¬ 2 ∣ d → sqrtCount (2 * r) (1 + r) (r / d) = 0) := by sorry

alias «FixedOrderFactor».«sqrtCount_imaginary'» := P2M_FixedOrderFactor_sqrtCount_imaginary__18e778af86a9
