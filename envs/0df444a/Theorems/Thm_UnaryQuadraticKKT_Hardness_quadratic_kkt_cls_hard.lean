-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_quadratic_kkt_cls_hard
-- name    : UnaryQuadraticKKT.Hardness.quadratic_kkt_cls_hard
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T02:56:13.804103+00:00
-- url     : https://prove2.me/theorems/02aa5fff-3118-59fd-93f3-2020a9733f9e
-- title:
--   Exact quadratic-KKT on the unit box is CLS-hard
-- statement:
--   Every problem in CLS reduces in polynomial time to the problem of finding an **exact** KKT point of a box-constrained quadratic program with rational data given in binary. Here a KKT point of $\min_{x\in[0,1]^n}\tfrac12x^\top Qx+c^\top x$ means: $x\in[0,1]^n$ and, with $F=Qx+c$, $x_i>0\Rightarrow F_i\le0$ and $x_i<1\Rightarrow F_i\ge0$. In symbols,
--   $$\mathrm{CLSHard}(\textsc{QuadraticKKT}).$$
--
--   This is the hardness half of the main result of Fearnley, Goldberg, Hollender and Savani, *The Complexity of Computing KKT Solutions of Quadratic Programs*. It is the binary starting point of the unary hardness proof (Theorem 4.1) of Anagnostides–Panageas–Yan.
--
--   **Formalization Note** Hardness is stated for the unbounded answer relation `quadraticSearch`, in which every exact KKT point is an answer. The reduction's decoder must therefore handle answers of any length. This is the form that composes with the binary-to-unary reduction. The sibling background statement `quadratic_cls_background` asserts hardness only for a length-bounded variant, which does not transfer upward.
-- source:
--   Fearnley–Goldberg–Hollender–Savani, The Complexity of Computing KKT Solutions of Quadratic Programs, arXiv:2311.13738v2, p.3, Main Result (unit-box clause); used as Theorem 3.3 in Anagnostides–Panageas–Yan, The Complexity of KKT Points of Quadratic Programs with Polynomially-Bounded Coefficients, STOC 2027 submission #653 (October 2026), Theorem 4.1 (p.5) and Section 4.5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace UnaryQuadraticKKT.Hardness
theorem quadratic_kkt_cls_hard : CLSHard quadraticSearch := by sorry
end UnaryQuadraticKKT.Hardness
