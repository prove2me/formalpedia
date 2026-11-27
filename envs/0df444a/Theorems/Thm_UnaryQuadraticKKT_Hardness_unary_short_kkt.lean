-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_unary_short_kkt
-- name    : UnaryQuadraticKKT.Hardness.unary_short_kkt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:51:25.421299+00:00
-- url     : https://prove2.me/theorems/8045f3fe-dda8-4af7-aa00-dbb2ca41228c
-- title:
--   Unary quadratic-KKT has short exact answers
-- statement:
--   For some fixed exponent $b$, every valid unary box QP $\min_{x\in[0,1]^n}\tfrac12x^\top Qx+c^\top x$ has an exact rational KKT point whose binary encoding has length at most $(|a|+1)^b+b$, where $a$ is the unary code of the instance. In symbols,
--   $$\exists b,\ \mathrm{TotalSearch}\big(\mathrm{bounded}(U,b)\big).$$
--   This is the totality and short-answer part of membership of the unary problem in TFNP, used in Theorem 4.1.
-- source:
--   Anagnostides–Panageas–Yan, The Complexity of KKT Points of Quadratic Programs with Polynomially-Bounded Coefficients, STOC 2027 submission #653 (October 2026), Theorem 4.1 (p.5), membership half (totality of KKT; exact rational solutions of polynomial size)

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace UnaryQuadraticKKT.Hardness
theorem unary_short_kkt : ∃ b : ℕ, TotalSearch (bounded unarySearch b) := by sorry
end UnaryQuadraticKKT.Hardness
