-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_top_dichotomy__7a2906f2d2a7
-- name    : P2M_FixedOrderFactor_sqrtCount_top_dichotomy__7a2906f2d2a7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:10.938412+00:00
-- url     : https://prove2.me/theorems/d506590c-3652-479c-bddb-846388861a26
-- title:
--   P2 M Fixed Order Factor sqrt Count top dichotomy  7a2906f2d2a7: P2 M Fixed Order Factor sqrt Count top dichotomy  7a2906f2d2a7
-- statement:
--   **The class criterion at the top level.** `β(M, a, r)` is `0` unless `a` is the square of an
--   element of `H`, and then it equals `β(M, 1, r)`, the number of square roots of `1` in `H`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L186-L218
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L186-L218

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]

theorem P2M_FixedOrderFactor_sqrtCount_top_dichotomy__7a2906f2d2a7 {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = if ∃ h : ZMod M, IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1
      then sqrtCount M 1 r else 0 := by sorry

alias «FixedOrderFactor».«sqrtCount_top_dichotomy'» := P2M_FixedOrderFactor_sqrtCount_top_dichotomy__7a2906f2d2a7
