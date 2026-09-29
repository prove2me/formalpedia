-- Prove2me | Theorems.Thm_VectorCalculus_conservative_iff_closed_line_integrals_vanish
-- name    : VectorCalculus.conservative_iff_closed_line_integrals_vanish
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T00:07:15.926863+00:00
-- url     : https://prove2.me/theorems/66928f3a-ea07-45a7-8382-8238757ba27f
-- title:
--   The line integral around any closed curve vanishes iff $\mathbf{F}$ is conservative
-- statement:
--   Let $\mathbf F$ be a continuous vector field on $\mathbb R^n$. Then the line integral of $\mathbf F$ around every closed $C^1$ curve vanishes,
--
--   $$\oint_C \mathbf F\cdot d\mathbf x = 0,$$
--
--   if and only if $\mathbf F$ is conservative, i.e. $\mathbf F = \nabla\phi$ for a continuous potential $\phi$ defined on all of $\mathbb R^n$. Here a closed curve is a continuously differentiable map $x:\mathbb R\to\mathbb R^n$ together with parameter values $a \le b$ satisfying $x(a) = x(b)$.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.2 (pp. 21–22), the Claim: "The line integral around any closed curve vanishes if and only if F is conservative"

import Definitions.Def_VectorCalculus_lineIntegral
import Definitions.Def_VectorCalculus_conservative

namespace VectorCalculus

theorem conservative_iff_closed_line_integrals_vanish {n : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (hF : Continuous F) :
    (∀ (x : ℝ → (Fin n → ℝ)) (a b : ℝ), a ≤ b → ContDiff ℝ 1 x → x a = x b →
      lineIntegral F x a b = 0) ↔ IsConservative F := by sorry

end VectorCalculus
