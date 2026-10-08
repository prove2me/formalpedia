-- Prove2me | Theorems.Thm_TalagrandConc_QPoints_eq_3_2_2
-- name    : TalagrandConc.QPoints.eq_3_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:26.310994+00:00
-- url     : https://prove2.me/theorems/34deb870-4243-4772-ae8f-5d6c45e2db96
-- title:
--   Eq. (3.2.2) — $a(q,\alpha)$ is the unique $x>1$ with $x+q\alpha x^{-1/\alpha}=1+q\alpha$
-- statement:
--   Let $q\ge2$ be an integer and $\alpha>1$ a real number, and let $a(q,\alpha)=\sup\{x>1: x+q\alpha x^{-1/\alpha}\le1+q\alpha\}$. Then $a(q,\alpha)>1$,
--   $$a(q,\alpha)+q\alpha\,a(q,\alpha)^{-1/\alpha}=1+q\alpha,$$
--   and every $x>1$ with $x+q\alpha x^{-1/\alpha}=1+q\alpha$ equals $a(q,\alpha)$.
--
--   This is the well-posedness of the constant $a(q,\alpha)$ that Talagrand introduces as "the unique number $x>1$" solving (3.2.2).
--
--   **Formalization Note** $x^{-1/\alpha}$ is the real power `Real.rpow`, used only for $x>1$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 114, Eq. (3.2.2)

import Mathlib
import Definitions.Def_TalagrandConc_QPoints_aConst

namespace TalagrandConc.QPoints

/-- (3.2.2): for `q ≥ 2` and `α > 1`, `a(q, α)` is the unique number `x > 1` with
`x + q α x^{-1/α} = 1 + q α`. -/
theorem eq_3_2_2 (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) :
    1 < aConst q α ∧
      aConst q α + (q : ℝ) * α * aConst q α ^ (-(1 / α)) = 1 + (q : ℝ) * α ∧
      ∀ x : ℝ, 1 < x → x + (q : ℝ) * α * x ^ (-(1 / α)) = 1 + (q : ℝ) * α →
        x = aConst q α := by sorry

end TalagrandConc.QPoints
