-- Prove2me | Theorems.Thm_VectorCalculus_closed_vanish_iff_path_independent
-- name    : VectorCalculus.closed_vanish_iff_path_independent
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T00:15:51.117924+00:00
-- url     : https://prove2.me/theorems/417d05c1-0b17-4daa-8745-36295d68b00f
-- title:
--   Vanishing circulation is equivalent to path independence
-- statement:
--   For a continuous vector field $\mathbf F$ on $\mathbb R^n$, the following are equivalent: the line integral of $\mathbf F$ around every closed $C^1$ curve vanishes; and the line integral of $\mathbf F$ depends only on the endpoints, i.e. any two $C^1$ curves with the same initial point and the same final point give the same integral. This is the reformulation with which §1.3 opens: $\int_{C_1} = \int_{C_2}$ for curves sharing endpoints and orientation is the same condition as $\oint_{C} = 0$ for the closed curve $C = C_1 - C_2$.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3 (p. 19), the equivalence of $\int_{C_1}\mathbf F\cdot d\mathbf x = \int_{C_2}\mathbf F\cdot d\mathbf x$ with $\oint_C \mathbf F\cdot d\mathbf x = 0$ for $C = C_1 - C_2$

import Definitions.Def_VectorCalculus_lineIntegral

namespace VectorCalculus

theorem closed_vanish_iff_path_independent {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : Continuous F) :
    (∀ (x : ℝ → (Fin n → ℝ)) (a b : ℝ), a ≤ b → ContDiff ℝ 1 x → x a = x b →
        lineIntegral F x a b = 0) ↔
      (∀ (x y : ℝ → (Fin n → ℝ)) (a b c d : ℝ), a ≤ b → c ≤ d →
        ContDiff ℝ 1 x → ContDiff ℝ 1 y → x a = y c → x b = y d →
        lineIntegral F x a b = lineIntegral F y c d) := by sorry

end VectorCalculus
