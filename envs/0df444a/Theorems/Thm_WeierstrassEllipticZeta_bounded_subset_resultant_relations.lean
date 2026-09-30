-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_resultant_relations
-- name    : WeierstrassEllipticZeta.bounded_subset_resultant_relations
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T15:07:41.663385+00:00
-- url     : https://prove2.me/theorems/e228afdd-f183-4b04-ba4d-f76d7e7f01da
-- title:
--   Bounded resultant relation certificates in the elliptic contact quotient
-- statement:
--   There is a positive constant $C$ depending only on the mission geometry $G$ with the following property. Take the exact parameters and assumptions of `bounded_subset_wp_univariate_jet_rank`: positive $m,n$, the prescribed finite range for $U\ge1$, a finite $X$ containing zero, a polynomial $Q$ of bidegree $(m,n)$, the stated nonzero local chart orders and analytic factorizations with order at least $3U+1$ on $X+X+X$, all chart-derivation degree bounds, and the chart certificates.
--
--   For every $Y\subseteq X$ containing zero with
--   $$|Y|=\left\lfloor\frac{Cmn^2}{U+1}\right\rfloor_++1,$$
--   put $Z=Y\setminus\Lambda$ and $N=3U+1$. Let $I$ be the intersection of the order-$N$ chart-zero contact ideals at $Z$, put $A=\mathbb C[X_0,X_1,X_2,X_3]/I$, and let $x\in A$ be the class of the elliptic coordinate $X_1$.
--
--   There exist $y\in A$, polynomials $F,H\in\mathbb C[X][Y]$, and nonnegative integers $a,b$ such that all coefficients of $F,H$ have $X$-degree at most $a,b$, respectively, at least one polynomial has positive $Y$-degree,
--   $$\operatorname{Res}_Y(F,H)\ne0,\qquad F(x,y)=H(x,y)=0\text{ in }A,$$
--   and
--   $$2\bigl((\deg_Y F)b+(\deg_Y H)a\bigr)+(U+1)\le Cn^2.$$
--
--   The relations must vanish in the contact quotient, including its nilpotents; vanishing only at the underlying points is insufficient. The full parent hypotheses, uniform constant, finite range, and subset threshold are retained. The proved resultant bound yields the parent rank estimate. A Lean converse chooses $y=0$, $F$ equal to the minimal polynomial of $x$ viewed as constant in $Y$, and $H=Y$, establishing equivalence with the same constant. The bounded relation construction remains open.
-- source:
--   Derived elimination step for https://prove2.me/theorems/2301083d-8664-4f21-b709-ebed43665718. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a general resultant bound applied to the already formalized contact quotient, not a claimed proof of the paper zero estimate. Primary Lean sources: Mathlib RingTheory/Polynomial/Resultant/Basic.lean (Sylvester determinant and Bezout identity), Algebra/Polynomial/BigOperators.lean (degrees of sums and products), RingTheory/Algebraic/Integral.lean, and RingTheory/Adjoin/PowerBasis.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The remaining construction asks for two relations with nonzero resultant and bounded elimination cost. It is equivalent to the selected rank estimate with the same uniform constant.

import Mathlib.RingTheory.Polynomial.Resultant.Basic
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

theorem WeierstrassEllipticZeta.bounded_subset_resultant_relations (G : Frontier.Geometry) :
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
              let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
                ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
                  (extensionChartCoordinates G.S 0 z.val) N
              let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
              ∃ (y : MvPolynomial (Fin 4) ℂ ⧸ I)
                (F H : Polynomial (Polynomial ℂ)) (a b : ℕ),
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                (∀ i, (H.coeff i).natDegree ≤ b) ∧
                (F.natDegree ≠ 0 ∨ H.natDegree ≠ 0) ∧
                F.resultant H ≠ 0 ∧
                F.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧
                H.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧
                ((2 * (F.natDegree * b + H.natDegree * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
