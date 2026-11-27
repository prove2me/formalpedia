-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_output_accounting
-- name    : UnaryQuadraticKKT.Hardness.output_accounting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:56:21.185144+00:00
-- url     : https://prove2.me/theorems/c2bb2cd9-58db-54ed-958f-8c2a2415b6c0
-- title:
--   Size accounting of the unary output QP (Theorem 4.1)
-- statement:
--   Let $P$ be a rational box QP of dimension $n\ge1$. Let $N$ be its binary payload length, $L$ the normalisation bit length, $t=|\mathrm{slots}(n)|$, $R$ the number of dyadic terms, and $A$ the number of auxiliary variables of the output QP $P_{\mathrm{out}}$. Then:
--
--   1. $L\le 2N+1$ and $R\le tL$;
--   2. $t\le 2n^2$ and $A\le R(L+2)$;
--   3. the output dimension is $n+A$;
--   4. the total absolute coefficient mass of the output polynomial is at most $200A$;
--   5. the output polynomial has at most $(n+A+1)(n+A+2)/2$ monomials;
--   6. the unary code of $P_{\mathrm{out}}$ has length at most $(n+A)+1+200A+8(n+A)^2$;
--   7. $P_{\mathrm{out}}$ has integer coefficients;
--   8. on the reindexed coordinates, the quadratic form of $P_{\mathrm{out}}$ equals the affine-substituted combined chain function minus the polynomial's constant term.
--
--   These are the quantitative conclusions of Theorem 4.1 and Section 4.5.
-- source:
--   Anagnostides–Panageas–Yan, The Complexity of KKT Points of Quadratic Programs with Polynomially-Bounded Coefficients, STOC 2027 submission #653 (October 2026), Theorem 4.1 (p.5) and Section 4.5, quantitative accounting

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace UnaryQuadraticKKT.Hardness
theorem output_accounting (n : ℕ) (hn : 0 < n) (p : Quadratic n) :
      normalizationLength p ≤ 2 * binaryDataLength p + 1 ∧
      (dyadicTerms p).length ≤ (slots n).length * normalizationLength p ∧
      (slots n).length ≤ 2 * n ^ 2 ∧
      auxiliaryCount p ≤ (dyadicTerms p).length * (normalizationLength p + 2) ∧
      outputDimension p = n + auxiliaryCount p ∧
      outputCoefficientMass p ≤ 200 * auxiliaryCount p ∧
      (outputPolynomial p).support.card ≤ (outputDimension p + 1) * (outputDimension p + 2) / 2 ∧
      (unaryCode (outputQuadratic p)).length ≤ outputDimension p + 1 +
        200 * auxiliaryCount p + 8 * outputDimension p ^ 2 ∧
      IntegerCoefficients (outputQuadratic p) ∧
      (∀ z : CombinedIndex p → ℝ,
        quadraticValue (outputQuadratic p) (fun i => z (coordinateAt p i)) =
          affineValue p z - (outputConstant p : ℝ)) := by sorry
end UnaryQuadraticKKT.Hardness
