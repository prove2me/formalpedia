-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_unary_quadratic_kkt_cls_complete
-- name    : UnaryQuadraticKKT.Hardness.unary_quadratic_kkt_cls_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:47:14.445544+00:00
-- url     : https://prove2.me/theorems/cb87f975-0b89-42ef-8bfe-d39c42b4419b
-- title:
--   Theorem 4.1 — unary exact Quadratic-KKT is CLS-complete, with integer-output hardness
-- statement:
--   Let $U$ be exact Quadratic-KKT with positive dimension and signed reduced rational numerator and denominator data encoded in unary as defined above. Let $U_{\mathbb Z}$ denote its integer-coefficient input subfamily, and let $\operatorname{bounded}_b(U)$ restrict only answer length to $(|a|+1)^b+b$ for input string $a$. Then
--   $$
--   (\exists b\in\mathbb N,\ \operatorname{InCLS}(\operatorname{bounded}_b(U)))\ \land\ \operatorname{CLSHard}(U)\ \land\ \operatorname{CLSHard}(U_{\mathbb Z}).
--   $$
--   CLS is the fixed public class of TFNP search problems reducing to 3D-Continuous-Localopt, including the Lipschitz-violation answers. Membership asserts totality, polynomial verification and a uniform sufficient rational answer bound. Hardness concerns the exact unbounded answer relation, without imposing a grid or selecting a particular KKT point.
--
--   The source's binary-to-unary reduction is also asserted concretely: there are two polynomial-time Cook machine maps $f$ and $g$, fixed before all inputs, such that $f(\operatorname{encBinary}(P))=\operatorname{encUnary}(P_{\rm out})$ for every positive-dimensional rational $P$. The resulting instance has integer coefficients. For every valid binary instance $a$ and every accepted answer $b$ of $f(a)$, $g(a,b)$ is an exact answer to $a$.
--
--   For every input $P$, put $t=|\operatorname{slots}(n)|$, $R=|\operatorname{dyadicTerms}(P)|$, and use the binary payload length $N$ defined above. The quantitative conclusions are
--   $$
--   L\le2N+1,\quad R\le tL,\quad t\le2n^2,\quad M_{\rm aux}\le R(L+2),\quad d=n+M_{\rm aux},\quad
--   \sum_{\alpha}|[X^\alpha]H|\le200M_{\rm aux}.
--   $$
--   The number of collected monomials is at most $(d+1)(d+2)/2$, including the constant, and the total unary output length is at most $d+1+200M_{\rm aux}+8d^2$. All output monomial coefficients are integers, and for every real vector $z$ on the combined coordinate type,
--   $$P_{\rm out}((z_{\operatorname{coordinateAt}(i)})_{i<d})=H(z)-h_0.$$
--   These conclusions incorporate the source's size accounting and actual construction time; none is an assumption. They retain all signed input coefficients, square and linear terms, the zero polynomial and all real KKT points. This classification is the mission's goal, with the existing Open binary classification retained as a supporting reference rather than a premise.
--
--   **Formalization Note** The output uses the explicit original-coordinate-first enumeration. Bounds count collected coefficients including constants. The scalar $h_0$ is removed only to return to Equation (2); the analytic $H$ keeps it. The runtime exponent is existential and uniform in the public machine predicate.
--
--   Differences from the source:
--   - generalization: the unary presentation identifies the input with polynomially bounded integer monomial coefficients → signed reduced rational numerators and positive denominators are encoded individually in unary; the integer subfamily is also CLS-hard; reason: this includes all source integer instances without assuming a polynomial unary length for a common denominator; membership uses unary-to-binary conversion and hardness already lands in integers
--   - encoding: the monomial convention of Equation (2) → the published objective ½xᵀQx+cᵀx with Q_ii=2q_ii and Q_ij=Q_ji=q_ij for i<j; reason: this invertible rational coefficient conversion preserves the entire polynomial and all its derivatives
--   - encoding: CLS-completeness for exact Quadratic-KKT → membership of bounded_b(U) for one uniform existential b, and CLS-hardness of the unbounded exact relation U and its integer subfamily; reason: the published InTFNP bounds every accepted answer, while the exact rational answer relation permits arbitrarily long encodings; totality, verification and a sufficient answer bound remain conclusions
--   - encoding: a polynomial-time binary-to-unary reduction in Section 4.5 → one Cook polynomial-time instance map computing the defined output and one Cook polynomial-time decoder correct for every accepted target answer; reason: the public machine runtime measures the original instance and target answer lengths; both maps and all exponents are uniform before all inputs
--   - encoding: the affine polynomial H can have a constant whereas Equation (2) has none → P_out equals H minus its computed constant h_0 in the explicit coordinate order; reason: subtracting a scalar leaves all derivatives and KKT points unchanged
--   - encoding: L=O(N), R=O(n²L), M_aux≤R(L+2), and polynomially bounded integer coefficients → L≤2N+1, R≤tL, t≤2n², M_aux≤R(L+2), d=n+M_aux, coefficient mass≤200M_aux, integer output coefficients, at most (d+1)(d+2)/2 collected monomials, unary output length at most d+1+200M_aux+8d², and exact output-value identity; reason: N charges every reduced source numerator and denominator bit and n; the conservative absolute-sum bound follows by expanding Equation (6) after u=2v−1; no runtime degree is invented
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Theorem 4.1, p.5, with its full reduction and size/runtime accounting in Section 4.5, pp.10–11. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness
open NetworkEquilibriumCLS.LinearNash

/-- Theorem 4.1, p.5, with its §4.5 integer-output reduction and quantitative accounting.
All complexity bounds in the published search-reduction interface are uniform machine bounds.
The Open binary-classification theorem is not assumed as a hypothesis. -/
theorem unary_quadratic_kkt_cls_complete :
    (∃ b : ℕ, InCLS (bounded unarySearch b)) ∧
    CLSHard unarySearch ∧ CLSHard unaryIntegerSearch ∧
    (∃ (f : List Bool → List Bool) (g : List (Option (Bool ⊕ Bool)) → List Bool),
      PolyTime f ∧ PolyTime g ∧
      (∀ (n : ℕ) (hn : 0 < n) (p : Quadratic n),
        f (encQuadratic p) = unaryCode (outputQuadratic p)) ∧
      (∀ a, quadraticSearch.valid a → unaryIntegerSearch.valid (f a) ∧
        ∀ b, unaryIntegerSearch.answer (f a) b → quadraticSearch.answer a (g (pairCode a b)))) ∧
    (∀ (n : ℕ) (hn : 0 < n) (p : Quadratic n),
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
          affineValue p z - (outputConstant p : ℝ))) := by sorry

end UnaryQuadraticKKT.Hardness
