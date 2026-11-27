-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_unary_membership
-- name    : UnaryQuadraticKKT.Hardness.unary_membership
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T02:56:15.532815+00:00
-- url     : https://prove2.me/theorems/6bb2ab66-66c4-5943-8d2f-c89c58eb723a
-- title:
--   Unary quadratic-KKT is in CLS
-- statement:
--   For some fixed exponent $b$, the problem of finding an exact KKT point of a box-constrained quadratic program whose coefficients are written in unary is in CLS. Answers are restricted to encoding length at most $(|a|+1)^b+b$. In symbols,
--   $$\exists b,\ \mathrm{InCLS}\big(\mathrm{bounded}(U,b)\big).$$
--   CLS membership means three things: the problem is total, answers are polynomial-time checkable, and it reduces in polynomial time to 3D-Continuous-Localopt.
--
--   This is the membership half of Theorem 4.1. The unary problem is a special case of the binary one, which lies in CLS by Fearnley–Goldberg–Hollender–Savani.
-- source:
--   Anagnostides–Panageas–Yan, The Complexity of KKT Points of Quadratic Programs with Polynomially-Bounded Coefficients, STOC 2027 submission #653 (October 2026), Theorem 4.1 (p.5) and Section 4.5; membership via Fearnley–Goldberg–Hollender–Savani, arXiv:2311.13738v2, p.3

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace UnaryQuadraticKKT.Hardness
theorem unary_membership : ∃ b : ℕ, InCLS (bounded unarySearch b) := by sorry
end UnaryQuadraticKKT.Hardness
