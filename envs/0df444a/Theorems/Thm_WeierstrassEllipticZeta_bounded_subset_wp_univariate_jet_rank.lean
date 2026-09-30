-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_wp_univariate_jet_rank
-- name    : WeierstrassEllipticZeta.bounded_subset_wp_univariate_jet_rank
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T03:47:34.572341+00:00
-- url     : https://prove2.me/theorems/2301083d-8664-4f21-b709-ebed43665718
-- title:
--   Quadratic rank bound for the explicit univariate elliptic jet matrix
-- statement:
--   There is a positive constant $C$ depending only on the geometry $G$ with the following property. Take the exact parameters and hypotheses of `bounded_subset_wp_jet_matrix_rank`: $m,n\ge1$, the prescribed finite range for $U\ge1$, a finite set $X$ containing zero, a bihomogeneous polynomial $Q$ of bidegree $(m,n)$, the nonzero local chart orders and analytic factorizations with order at least $3U+1$ on $X+X+X$, the bounds on all chart-derivation degrees, and the chart certificates.
--
--   For every $Y\subseteq X$ containing zero with
--   $$|Y|=\left\lfloor\frac{Cmn^2}{U+1}\right\rfloor_++1,$$
--   put $Z=Y\setminus\Lambda$, $N=3U+1$, and $D=N|Z|$. Define
--   $$Tp=(4X^3-g_2X-g_3)p''+(6X^2-g_2/2)p',\qquad q_{j,k}=T^{\lfloor j/2\rfloor}(X^k).$$
--   Form the matrix with rows $(z,j)\in Z\times\{0,\ldots,N-1\}$ and columns $0\le k<D$,
--   $$J_{(z,j),k}=\begin{cases}q_{j,k}(\wp(z)),&j\text{ even},\\ \wp'(z)q'_{j,k}(\wp(z)),&j\text{ odd}.\end{cases}$$
--   Then
--   $$2\operatorname{rank}_{\mathbb C}J+(U+1)\le Cn^2.$$
--
--   The proved jet formula identifies this matrix entry by entry with the parent's matrix. Thus the bound has exactly the same constant, row and column ranges, threshold, and hypotheses. The additional proved degree estimate gives $\deg q_{j,k}\le k+\lfloor j/2\rfloor$. The quantitative rank inequality itself remains open.
-- source:
--   Derived explicit jet construction for https://prove2.me/theorems/c86e9b67-82c2-40be-ab98-ad6551efe527. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. The construction uses the elliptic differential identities to evaluate even and odd chart jets using a single univariate polynomial recurrence, with a degree bound. It is a derived lemma, not a transcription or proof of the article zero estimate. Primary Lean sources: Mathlib Analysis/SpecialFunctions/Elliptic/Weierstrass.lean, Analysis/Calculus/Deriv/Polynomial.lean, Analysis/Calculus/IteratedDeriv/Lemmas.lean, and Algebra/Polynomial/Derivative.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The explicit univariate jet-matrix rank bound remains open. The proved formula identifies its matrix entry by entry with the parent matrix, so the bounds are equivalent with the identical uniform constant.

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.bounded_subset_wp_univariate_jet_rank (G : Frontier.Geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, ∀ U : Fin ((G.B (m + 2 * n) - 2) / 3 + 1),
          1 ≤ m → 1 ≤ n → 1 ≤ (U : ℕ) → ∀ X : Finset ℂ,
          0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
            (∀ d ∈ Q.support, d 0 + d 1 = m ∧
              d 2 + d 3 + d 4 + d 5 + d 6 = n) →
            (∀ (c : Fin 2) (z : ℂ), G.S (extensionChartDenominator c) z ≠ 0 →
              let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
                (extensionChartNormalize c Q)
              ∃! k : ℕ, k < G.B (m + 2 * n) ∧
                (z ∈ X + X + X → 3 * (U : ℕ) + 1 ≤ k) ∧
                (∀ j < k, iteratedDeriv j f z = 0) ∧ iteratedDeriv k f z ≠ 0 ∧
                ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
                  f =ᶠ[𝓝 z] (fun w => (w - z) ^ k * g w)) →
            (∀ (c : Fin 2) (k : ℕ),
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
                m + 2 * n + k) →
            Frontier.HasChartCertificates G m n (U : ℕ) X Q →
            ∀ Y : Finset ℂ, Y ⊆ X → 0 ∈ Y →
              Y.card = ⌊(C * (m : ℝ) * (n : ℝ) ^ 2) /
                (((U : ℕ) + 1 : ℕ) : ℝ)⌋₊ + 1 →
              let Z := Y.filter (fun z => z ∉ G.L.lattice)
              let N := 3 * (U : ℕ) + 1
              let T : Polynomial ℂ → Polynomial ℂ := fun q =>
                (Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C G.L.g₂ * Polynomial.X -
                  Polynomial.C G.L.g₃) * q.derivative.derivative +
                (Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C (G.L.g₂ / 2)) * q.derivative
              let J : Matrix (Z × Fin N) (Fin (N * Z.card)) ℂ := Matrix.of fun r k =>
                let q := T^[r.2.val / 2] (Polynomial.X ^ k.val)
                if r.2.val % 2 = 0 then q.eval (G.L.weierstrassP r.1.val)
                else G.L.derivWeierstrassP r.1.val * q.derivative.eval (G.L.weierstrassP r.1.val)
              ((2 * J.rank + ((U : ℕ) + 1) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ 2 := by sorry
