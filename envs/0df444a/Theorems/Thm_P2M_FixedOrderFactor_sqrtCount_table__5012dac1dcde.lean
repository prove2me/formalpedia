-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_table__5012dac1dcde
-- name    : P2M_FixedOrderFactor_sqrtCount_table__5012dac1dcde
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:03.639514+00:00
-- url     : https://prove2.me/theorems/ce205f2f-611d-580b-9d4d-2953f4fcbce8
-- title:
--   P2 M Fixed Order Factor sqrt Count table  5012dac1dcde: P2 M Fixed Order Factor sqrt Count table  5012dac1dcde
-- statement:
--   The predictions `β` of the table of Paper XI, Section 7 (families `p ≡ a (mod M)` and
--   `s = r/d(b)` for generic `b`, squares and fourth powers).
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L296-L311
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L296-L311

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor

theorem P2M_FixedOrderFactor_sqrtCount_table__5012dac1dcde :
    -- r = 2
    sqrtCount 16 1 2 = 4 ∧ sqrtCount 16 9 2 = 4 ∧ sqrtCount 8 5 2 = 0 ∧
    -- r = 3 (generic and squares: s = 3)
    sqrtCount 12 1 3 = 2 ∧ sqrtCount 12 7 3 = 0 ∧
    -- r = 4 (generic s = 4, squares s = 2)
    sqrtCount 8 5 4 = 0 ∧ sqrtCount 8 5 2 = 0 ∧
    sqrtCount 16 1 4 = 2 ∧ sqrtCount 16 1 2 = 4 ∧ sqrtCount 16 9 4 = 2 ∧ sqrtCount 16 9 2 = 4 ∧
    -- r = 6 (generic s = 6, squares s = 3)
    sqrtCount 12 1 6 = 2 ∧ sqrtCount 12 1 3 = 2 ∧ sqrtCount 12 7 6 = 0 ∧ sqrtCount 12 7 3 = 0 ∧
    -- r = 8 (generic s = 8, squares s = 4, fourth powers s = 2)
    sqrtCount 16 1 8 = 2 ∧ sqrtCount 16 1 4 = 2 ∧ sqrtCount 16 1 2 = 4 ∧
    sqrtCount 16 9 8 = 0 ∧ sqrtCount 16 9 4 = 2 ∧ sqrtCount 16 9 2 = 4 ∧
    sqrtCount 32 17 8 = 2 ∧ sqrtCount 32 17 4 = 2 ∧ sqrtCount 32 17 2 = 4 ∧
    sqrtCount 32 25 8 = 0 ∧ sqrtCount 32 25 4 = 2 ∧ sqrtCount 32 25 2 = 4 := by sorry

alias «FixedOrderFactor».«sqrtCount_table'» := P2M_FixedOrderFactor_sqrtCount_table__5012dac1dcde
