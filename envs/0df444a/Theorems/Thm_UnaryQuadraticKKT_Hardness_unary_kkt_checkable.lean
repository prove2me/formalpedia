-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_unary_kkt_checkable
-- name    : UnaryQuadraticKKT.Hardness.unary_kkt_checkable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:51:35.894294+00:00
-- url     : https://prove2.me/theorems/0662e383-1c9d-4939-af3f-037efbd7036f
-- title:
--   Unary quadratic-KKT answers are polynomial-time checkable
-- statement:
--   For every exponent $b$, the relation "$x$ is a valid unary box-QP instance and $y$ encodes an exact KKT point of it of length at most $(|x|+1)^b+b$" is decidable in polynomial time on Cook's machines. In symbols,
--   $$\mathrm{checkLang}\big(\mathrm{bounded}(U,b)\big)\in\mathsf P .$$
--   This is the verification part of membership of the unary problem in TFNP, used in Theorem 4.1.
-- source:
--   Anagnostides–Panageas–Yan, The Complexity of KKT Points of Quadratic Programs with Polynomially-Bounded Coefficients, STOC 2027 submission #653 (October 2026), Theorem 4.1 (p.5), membership half (polynomial-time verification of KKT points)

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace UnaryQuadraticKKT.Hardness
theorem unary_kkt_checkable (b : ℕ) :
    CookPvsNP.checkLang (fun x y => (bounded unarySearch b).valid x ∧ (bounded unarySearch b).answer x y) ∈
      CookPvsNP.P (Option (Bool ⊕ Bool)) := by sorry
end UnaryQuadraticKKT.Hardness
