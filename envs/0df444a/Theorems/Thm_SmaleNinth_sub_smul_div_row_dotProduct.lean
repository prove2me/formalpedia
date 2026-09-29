-- Prove2me | Theorems.Thm_SmaleNinth_sub_smul_div_row_dotProduct
-- name    : SmaleNinth.sub_smul_div_row_dotProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T08:28:17.542329+00:00
-- url     : https://prove2.me/theorems/0727d086-bbd4-41ea-8dd4-ebc9f4ff843a
-- title:
--   Subtracting a scaled normalized row commutes with a row dot product
-- statement:
--   For finite real rows $u,v,w$ and real scalars $a,d$, the dot product of the pointwise row $u-a(v/d)$ with $w$ equals the dot product of $u$ with $w$ minus $a$ times the dot product of $v$ with $w$, divided by $d$. This is the non-pivot-row algebra used by a rectangular Gauss--Jordan operation.
-- source:
--   Mathlib/Data/Matrix/Mul.lean, `sub_dotProduct` and `smul_dotProduct`, together with the proved row-division identity `SmaleNinth.div_row_dotProduct`.

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Theorems.Thm_SmaleNinth_div_row_dotProduct

open Matrix

theorem SmaleNinth.sub_smul_div_row_dotProduct {n : ℕ}
    (u v w : Fin n → ℝ) (a d : ℝ) :
    ((fun k => u k - a * (v k / d)) ⬝ᵥ w) =
      (u ⬝ᵥ w) - a * ((v ⬝ᵥ w) / d) := by sorry
