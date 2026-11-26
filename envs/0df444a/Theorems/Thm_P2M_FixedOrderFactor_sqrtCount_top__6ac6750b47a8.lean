-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_top__6ac6750b47a8
-- name    : P2M_FixedOrderFactor_sqrtCount_top__6ac6750b47a8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:25.321655+00:00
-- url     : https://prove2.me/theorems/088cf62e-9728-56a6-ba42-a5a9188e89f3
-- title:
--   P2 M Fixed Order Factor sqrt Count top  6ac6750b47a8: P2 M Fixed Order Factor sqrt Count top  6ac6750b47a8
-- statement:
--   **At the top level** (`s = r`, the `b` with `d(b) = 1`): `x ↦ -x` identifies `β(M, a, r)` with
--   the number of square roots of `a` in `H = {h ∈ (ℤ/M)ˣ : h ≡ 1 (mod r)}`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L168-L182
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L168-L182

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]

theorem P2M_FixedOrderFactor_sqrtCount_top__6ac6750b47a8 {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = (univ.filter fun h : ZMod M =>
      IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1).card := by sorry

alias «FixedOrderFactor».«sqrtCount_top'» := P2M_FixedOrderFactor_sqrtCount_top__6ac6750b47a8
