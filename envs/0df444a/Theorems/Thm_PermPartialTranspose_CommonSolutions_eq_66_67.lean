-- Prove2me | Theorems.Thm_PermPartialTranspose_CommonSolutions_eq_66_67
-- name    : PermPartialTranspose.CommonSolutions.eq_66_67
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:33.963475+00:00
-- url     : https://prove2.me/theorems/1ad4497b-8acb-4602-9cca-ff3ec0ea0b26
-- title:
--   (66)–(67): two flat braid representations in dimension two
-- statement:
--   In dimension two, let $P$ be permutation and $P^*=\mathbf1-\Theta_2(P)$. Write $P_i,P_{i+1}$ and $P_i^*,P_{i+1}^*$ for their actions on adjacent pairs in $V^{\otimes3}$. Both $P$ and $P^*$ satisfy the braid relation, both square to the identity, and
--
--   $$\begin{aligned}
--   P_iP^*_{i+1}P_i&=P_{i+1}P_i^*P_{i+1},\\
--   P_iP^*_{i+1}P_i^*&=P^*_{i+1}P_i^*P_{i+1},\\
--   P_i^*P^*_{i+1}P_i&=P_{i+1}P_i^*P^*_{i+1}.
--   \end{aligned}$$
--
--   These are the paper's flat unrestricted braid relations with $P^*$ as the flat crossing and $P$ as the virtual crossing.
-- source:
--   Zhang, Kauffman & Werner, Permutation and Its Partial Transpose, arXiv:quant-ph/0606005v1, p. 22, (66)–(67)

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

namespace PermPartialTranspose.CommonSolutions

/-- Equations (66)–(67), p. 22. -/
theorem eq_66_67 :
    BraidRel (swapOp 2) ∧
    BraidRel (pBar 2) ∧
    swapOp 2 * swapOp 2 = 1 ∧
    pBar 2 * pBar 2 = 1 ∧
    onFirst (swapOp 2) * onLast (pBar 2) * onFirst (swapOp 2) =
      onLast (swapOp 2) * onFirst (pBar 2) * onLast (swapOp 2) ∧
    onFirst (swapOp 2) * onLast (pBar 2) * onFirst (pBar 2) =
      onLast (pBar 2) * onFirst (pBar 2) * onLast (swapOp 2) ∧
    onFirst (pBar 2) * onLast (pBar 2) * onFirst (swapOp 2) =
      onLast (swapOp 2) * onFirst (pBar 2) * onLast (pBar 2) := by sorry

end PermPartialTranspose.CommonSolutions
