-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_eq_28_29
-- name    : QMaxCutBeyond.TwoQubit.eq_28_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:16.65299+00:00
-- url     : https://prove2.me/theorems/651a86cb-6559-4229-9c14-882cf80800a9
-- title:
--   Eqs. (28)–(29) — min over 0 ≤ x ≤ y ≤ 1 of max{2y, 3x+1, (4+x+y)/3}/(2+y+x) is at least 0.55
-- statement:
--   For all real $x,y$ with $0\le x\le y\le 1$,
--   $$\frac{1}{2+y+x}\max\Bigl\{2y,\;3x+1,\;\tfrac13(4+x+y)\Bigr\}\;\ge\;0.55 ,$$
--   that is, $\min_{0\le x\le y\le1}\frac{1}{2+y+x}\max\{2y,3x+1,\frac13(4+x+y)\}\ge0.55$.
--
--   With $x=m/W$ and $y=f/W$ this turns eq. (27) into the constant $0.55$ of Theorem 3; the paper evaluates the minimum by computer.
--
--   **Formalization Note** Stated pointwise on the paper's domain without division (the denominator $2+y+x$ is positive there): $\frac{11}{20}(2+y+x)\le\max\{2y,3x+1,(4+x+y)/3\}$.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 11, eqs. (28)–(29), proof of Theorem 3

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Eqs. (28)–(29), p. 11: `min_{0≤x≤y≤1} max{2y, 3x + 1, (4 + x + y)/3} / (2 + y + x) ≥ 0.55`,
stated pointwise on the domain without division. -/
theorem eq_28_29 (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (11 / 20 : ℝ) * (2 + y + x) ≤ max (2 * y) (max (3 * x + 1) ((4 + x + y) / 3)) := by sorry

end QMaxCutBeyond.TwoQubit
