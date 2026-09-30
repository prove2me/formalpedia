-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_wp_chart_jet_univariate_formula
-- name    : WeierstrassEllipticZeta.wp_chart_jet_univariate_formula
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T03:47:31.354176+00:00
-- url     : https://prove2.me/theorems/5092caad-9b92-45c6-bc6d-fc41cc04e87a
-- title:
--   Univariate formulas and degree bounds for elliptic chart jets
-- statement:
--   Let $G$ be the mission's elliptic chart geometry, let $z$ be outside its period lattice, and let $p\in\mathbb C[X]$ and $j\ge0$. Define the polynomial operator
--   $$Tp=(4X^3-g_2X-g_3)p''+(6X^2-g_2/2)p'.$$
--   Put $q=T^{\lfloor j/2\rfloor}p$. Then
--   $$\operatorname{natDegree}q\le\operatorname{natDegree}p+\lfloor j/2\rfloor,$$
--   and the order-$j$ chart-zero jet of $p(X_1)$ at $z$ is
--   $$\begin{cases}q(\wp(z)),&j\text{ even},\\ \wp'(z)q'(\wp(z)),&j\text{ odd}.\end{cases}$$
--   Here the chart jet means evaluation at the chart coordinates of the $j$th iterate of the mission's chart derivation applied to the image of $p$ under $X\mapsto X_1$. The proof identifies it with the ordinary derivative of $p(\wp(z))$.
--
--   The statement includes $p=0$, constant polynomials, order zero, and zeros of $\wp'$. Lean's natural degree of the zero polynomial is zero. No division by $\wp'$ is used. The operator depends only on the lattice invariants, and the displayed entries use the canonical functions $\wp$ and $\wp'$.
-- source:
--   Derived explicit jet construction for https://prove2.me/theorems/c86e9b67-82c2-40be-ab98-ad6551efe527. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. The construction uses the elliptic differential identities to evaluate even and odd chart jets using a single univariate polynomial recurrence, with a degree bound. It is a derived lemma, not a transcription or proof of the article zero estimate. Primary Lean sources: Mathlib Analysis/SpecialFunctions/Elliptic/Weierstrass.lean, Analysis/Calculus/Deriv/Polynomial.lean, Analysis/Calculus/IteratedDeriv/Lemmas.lean, and Algebra/Polynomial/Derivative.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The explicit univariate jet-matrix rank bound remains open. The proved formula identifies its matrix entry by entry with the parent matrix, so the bounds are equivalent with the identical uniform constant.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.ComputeDegree

noncomputable section
open WeierstrassEllipticZeta Polynomial
open scoped Classical Topology

theorem WeierstrassEllipticZeta.wp_chart_jet_univariate_formula
    (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) (p : Polynomial ℂ) (j : ℕ) :
    let T : Polynomial ℂ → Polynomial ℂ := fun q =>
      (Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C G.L.g₂ * Polynomial.X -
        Polynomial.C G.L.g₃) * q.derivative.derivative +
      (Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C (G.L.g₂ / 2)) * q.derivative
    let q := T^[j / 2] p
    q.natDegree ≤ p.natDegree + j / 2 ∧
    MvPolynomial.eval (extensionChartCoordinates G.S 0 z)
      ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[j]
        (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) p)) =
      if j % 2 = 0 then q.eval (G.L.weierstrassP z)
      else G.L.derivWeierstrassP z * q.derivative.eval (G.L.weierstrassP z) := by sorry
