-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_eq_card_zmod__2e6db6efff87
-- name    : P2M_FixedOrderFactor_sqrtCount_eq_card_zmod__2e6db6efff87
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:04.30878+00:00
-- url     : https://prove2.me/theorems/5856b1ff-23b7-5216-952d-48bd83f30e69
-- title:
--   P2 M Fixed Order Factor sqrt Count eq card zmod  2e6db6efff87: P2 M Fixed Order Factor sqrt Count eq card zmod  2e6db6efff87
-- statement:
--   **The residue-class reading.** For `M > 0` and `s ∣ M`, `β(M, a, s)` counts the units `y` of
--   `ℤ/M` with `y² = a` and `y ≡ -1 (mod s)`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L121-L143
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L121-L143

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]

theorem P2M_FixedOrderFactor_sqrtCount_eq_card_zmod__2e6db6efff87 {s : ℕ} (hs : s ∣ M) (a : ℕ) :
    sqrtCount M a s = (univ.filter fun y : ZMod M =>
      IsUnit y ∧ y ^ 2 = a ∧ ZMod.castHom hs (ZMod s) y = -1).card := by sorry

alias «FixedOrderFactor».«sqrtCount_eq_card_zmod'» := P2M_FixedOrderFactor_sqrtCount_eq_card_zmod__2e6db6efff87
