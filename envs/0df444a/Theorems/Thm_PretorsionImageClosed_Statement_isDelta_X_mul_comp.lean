-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isDelta_X_mul_comp
-- name    : PretorsionImageClosed.Statement.isDelta_X_mul_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:10:29.119203+00:00
-- url     : https://prove2.me/theorems/ec4b99a6-64b4-4a68-9f56-c78872ca712e
-- title:
--   Statement: is Delta X mul comp
-- statement:
--   For `G = Δ_q g`: `Δ_q(x · g(U)) = g(U) + q U · G(U)`, where `U = 1 + qx`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L210-L217
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L210-L217

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial

theorem PretorsionImageClosed.Statement.isDelta_X_mul_comp {g G : Rq[X]} (hG : IsDelta g G) :
    IsDelta (X * g.comp U) (g.comp U + C q * U * G.comp U) := by sorry
