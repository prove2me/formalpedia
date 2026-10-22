-- Prove2me | Theorems.Thm_PermPartialTranspose_CommonSolutions_eq_127
-- name    : PermPartialTranspose.CommonSolutions.eq_127
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:32.157273+00:00
-- url     : https://prove2.me/theorems/5313c7a5-1af9-480a-b1c0-ea770e3e7a60
-- title:
--   (127): necessary coefficient equations above dimension two
-- statement:
--   Let $d>2$, and let $\check R(t)=a\mathbf1+tP+bP_*$ with complex $a,b,u,v$. If the additive Yang–Baxter equality holds at this particular pair $(u,v)$, then
--
--   $$\begin{aligned}
--   abu&=ab(u+v)+b^2v,\\
--   abv&=ab(u+v)+b^2u,\\
--   a^2b&=ab(u+v)+b^2(u+v)+b^3+2a^2b+ab^2d.
--   \end{aligned}$$
--
--   These are the coefficient constraints extracted in Appendix B. The statement gives the necessary direction asserted by the paper; it makes no uniqueness claim at fixed $(u,v)$.
--
--   **Formalization Note** The hypothesis $3\le d$ is the natural-number form of the paper's $d>2$.
-- source:
--   Zhang, Kauffman & Werner, Permutation and Its Partial Transpose, arXiv:quant-ph/0606005v1, p. 38, Appendix B, (127)

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

namespace PermPartialTranspose.CommonSolutions

/-- The necessary coefficient equations (127), Appendix B, p. 38. -/
theorem eq_127 (d : ℕ) (hd : 3 ≤ d) (a b u v : ℂ)
    (h : onFirst (Rcheck d a u b) * onLast (Rcheck d a (u + v) b) *
          onFirst (Rcheck d a v b) =
        onLast (Rcheck d a v b) * onFirst (Rcheck d a (u + v) b) *
          onLast (Rcheck d a u b)) :
    a * b * u = a * b * (u + v) + b ^ 2 * v ∧
    a * b * v = a * b * (u + v) + b ^ 2 * u ∧
    a ^ 2 * b = a * b * (u + v) + b ^ 2 * (u + v) + b ^ 3 +
      2 * a ^ 2 * b + a * b ^ 2 * (d : ℂ) := by sorry

end PermPartialTranspose.CommonSolutions
