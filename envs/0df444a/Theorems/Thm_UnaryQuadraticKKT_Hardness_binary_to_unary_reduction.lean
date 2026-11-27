-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_binary_to_unary_reduction
-- name    : UnaryQuadraticKKT.Hardness.binary_to_unary_reduction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T02:56:11.513638+00:00
-- url     : https://prove2.me/theorems/aec15191-dd0f-5f41-87d3-c652bcb14f6d
-- title:
--   Binary-to-unary integer reduction for quadratic KKT (Section 4.5)
-- statement:
--   There are polynomial-time maps $f$ and $g$ on Cook's machines with two properties.
--
--   1. $f$ sends the binary code of every positive-dimensional rational box QP $P$ to the unary code of the integer QP $P_{\mathrm{out}}$ built in Section 4. $P_{\mathrm{out}}$ is obtained by normalising $P$, expanding its coefficients in binary, and replacing every dyadic monomial by a chain gadget (Eq. (6), (16), (19)).
--   2. For every valid binary instance $a$ and every exact KKT point $b$ of the unary instance $f(a)$, $g(a,b)$ is an exact KKT point of $a$.
--
--   This is the polynomial-time reduction of Section 4.5, which transfers the CLS-hardness of exact quadratic KKT from binary to unary, integer-coefficient inputs.
-- source:
--   Anagnostides–Panageas–Yan, The Complexity of KKT Points of Quadratic Programs with Polynomially-Bounded Coefficients, STOC 2027 submission #653 (October 2026), Theorem 4.1 (p.5) and Section 4.5, Section 4.5 (integer output) and Proposition 4.6 / Eq. (19)

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace UnaryQuadraticKKT.Hardness
theorem binary_to_unary_reduction :
    ∃ (f : List Bool → List Bool) (g : List (Option (Bool ⊕ Bool)) → List Bool),
      PolyTime f ∧ PolyTime g ∧
      (∀ (n : ℕ) (hn : 0 < n) (p : Quadratic n),
        f (encQuadratic p) = unaryCode (outputQuadratic p)) ∧
      (∀ a, quadraticSearch.valid a → unaryIntegerSearch.valid (f a) ∧
        ∀ b, unaryIntegerSearch.answer (f a) b → quadraticSearch.answer a (g (pairCode a b))) := by sorry
end UnaryQuadraticKKT.Hardness
