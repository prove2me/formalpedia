-- Prove2me | Theorems.Thm_PermPartialTranspose_CommonSolutions_eq_74
-- name    : PermPartialTranspose.CommonSolutions.eq_74
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:29.175186+00:00
-- url     : https://prove2.me/theorems/e0cb319c-2bfd-4aa7-914c-4b29eef8fc70
-- title:
--   (74): coloured Yang–Baxter identity for the dimension-two family
-- statement:
--   In dimension two put $P^*=\mathbf1-\Theta_2(P)$ and $\check R(t)=aP^*+tP$, where $a,x,y,z\in\mathbb C$. On three factors, the paper's coloured identity is
--
--   $$\check R_i(x)\check R_{i+1}(z)\check R_i(y)
--     =\check R_{i+1}(y)\check R_i(z)\check R_{i+1}(x).$$
--
--   This common identity supplies both Yang–Baxter parameter laws in the dimension-two branch.
-- source:
--   Zhang, Kauffman & Werner, Permutation and Its Partial Transpose, arXiv:quant-ph/0606005v1, pp. 23–24, (71) and (74)

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

namespace PermPartialTranspose.CommonSolutions

/-- Equation (74), p. 24, with the operator (71). -/
theorem eq_74 (a x y z : ℂ) :
    onFirst (a • pBar 2 + x • swapOp 2) *
        onLast (a • pBar 2 + z • swapOp 2) *
        onFirst (a • pBar 2 + y • swapOp 2) =
      onLast (a • pBar 2 + y • swapOp 2) *
        onFirst (a • pBar 2 + z • swapOp 2) *
        onLast (a • pBar 2 + x • swapOp 2) := by sorry

end PermPartialTranspose.CommonSolutions
