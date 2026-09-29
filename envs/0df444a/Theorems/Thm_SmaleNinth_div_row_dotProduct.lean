-- Prove2me | Theorems.Thm_SmaleNinth_div_row_dotProduct
-- name    : SmaleNinth.div_row_dotProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T08:03:25.248152+00:00
-- url     : https://prove2.me/theorems/ce13fea7-5def-4da3-b236-ea3a89d1a1ed
-- title:
--   Division commutes with a finite row dot product
-- statement:
--   For finite real rows $u$ and $z$ and any real scalar $d$, dividing every entry of the first row by $d$ before taking its dot product with $z$ has the same result as taking the dot product first and dividing the result by $d$. The identity is a finite-sum distribution fact and does not require $d
--   e0$; with Lean's totalized division it also holds at $d=0$.
-- source:
--   Standard finite-sum algebra in the pinned Mathlib environment; Mathlib/Algebra/BigOperators/Field.lean, `Finset.sum_div`, and Mathlib/Data/Matrix/Mul.lean, `dotProduct`.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

open Matrix

theorem SmaleNinth.div_row_dotProduct {n : ℕ}
    (u z : Fin n → ℝ) (d : ℝ) :
    ((fun k => u k / d) ⬝ᵥ z) = (u ⬝ᵥ z) / d := by sorry
