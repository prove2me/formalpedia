-- Prove2me | Theorems.Thm_PermPartialTranspose_CommonSolutions_tl_identities
-- name    : PermPartialTranspose.CommonSolutions.tl_identities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:24.551319+00:00
-- url     : https://prove2.me/theorems/6d93d577-1816-4839-9343-459d0a15e919
-- title:
--   §2.1 and (7): identities of the partial transpose of permutation
-- statement:
--   Let $P$ exchange the two factors of $\mathbb C^d\otimes\mathbb C^d$, and let $P_*=\Theta_2(P)$ be its partial transpose in the second factor. Then
--
--   $$PP_*=P_*P=P_*,\qquad P_*^2=dP_*.$$
--
--   These are the multiplication identities used when $P_*$ is viewed as a Temperley–Lieb generator.
-- source:
--   Zhang, Kauffman & Werner, Permutation and Its Partial Transpose, arXiv:quant-ph/0606005v1, pp. 5–6, §2.1 and (7)

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

namespace PermPartialTranspose.CommonSolutions

/-- §2.1, p. 5 and equation (7), p. 6. -/
theorem tl_identities (d : ℕ) :
    swapOp d * pStar d = pStar d ∧
    pStar d * swapOp d = pStar d ∧
    pStar d * pStar d = (d : ℂ) • pStar d := by sorry

end PermPartialTranspose.CommonSolutions
