-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_power_cost_polynomial
-- name    : QAlgorithms.Papers.Independent.Support50.P35.power_cost_polynomial
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:47:34.1361+00:00
-- url     : https://prove2.me/theorems/05134eff-8baa-4bd4-8379-a4c2685a897a
-- title:
--   Power costs are polynomials in every Hermitian operator basis
-- statement:
--   Let \(1\leq N\leq M\) and \(a\in\mathbb N\), \(a>1\). Use complete norm-one Gellmann bases \(\lambda^A_\alpha,\lambda^B_\beta\), with zero denoting the identity label. For real tensor coordinates \(c\), put \(R(c)=\sum_{\alpha\beta}c_{\alpha\beta}\lambda^A_\alpha\otimes\lambda^B_\beta\). Then
--
--   $$
--   \operatorname{tr}_B R(c)=\sqrt N\sum_\alpha c_{\alpha0}\lambda^A_\alpha=:A(c),\qquad
--   f_a(\operatorname{tr}_B R(c))=2\bigl(1-\operatorname{tr}(A(c)^a)\bigr).
--   $$
--
--   For any complete Hermitian orthonormal basis \(\nu_k\) of the bipartite operator space, there exists a real polynomial \(P\) in its \((MN)^2\) unscaled coordinates such that \(P(d)=f_a(\operatorname{tr}_B\sum_kd_k\nu_k)\) for every real \(d\). If \(O_{(\alpha,\beta),k}=\operatorname{tr}(\nu_k(\lambda^A_\alpha\otimes\lambda^B_\beta))\), the same marginal formula holds with \(c=Od\). The factor \(\sqrt N\) corrects Eqs.(58)--(59) because \(\operatorname{tr}\lambda^B_0=\sqrt N\). This gives a polynomial extension of the pure-state entanglement cost in every such coordinate basis.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 18, Unnumbered Eqs.(57)–(59): polynomial entanglement in any operator coordinates

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.18, Eqs.(57)--(59): the corrected marginal/cost formula and a
real polynomial in ANY Hermitian orthonormal operator coordinates. -/
theorem power_cost_polynomial (M N a : ℕ) (hN : 0 < N) (hNM : N ≤ M) (ha : 1 < a)
    (nu : Fin ((M * N) ^ 2) → Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ)
    (hnu : IsHermitianONBasis nu) :
    (∀ c : FullIndex M × FullIndex N → ℝ,
      traceRight (hermitianReconstruction (tensorGellmannBasis M N) c) = tensorMarginal c ∧
      powerPurityCost a (traceRight (hermitianReconstruction (tensorGellmannBasis M N) c)) =
        2 * (1 - (tensorMarginal c ^ a).trace.re)) ∧
    (∃ P : MvPolynomial (Fin ((M * N) ^ 2)) ℝ,
      ∀ d : Fin ((M * N) ^ 2) → ℝ,
        MvPolynomial.eval d P = powerPurityCost a (traceRight (hermitianReconstruction nu d)) ∧
        traceRight (hermitianReconstruction nu d) = tensorMarginal
          ((basisChange (tensorGellmannBasis M N) nu).mulVec d)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
