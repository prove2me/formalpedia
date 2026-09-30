-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_resultant_families
-- name    : WeierstrassEllipticZeta.bounded_subset_resultant_families
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T15:50:49.02202+00:00
-- url     : https://prove2.me/theorems/08ae25ab-c63e-48d2-ab17-5189a85148d9
-- title:
--   Bounded root-avoiding relation families in the elliptic contact quotient
-- statement:
--   Retain the geometry, auxiliary-polynomial hypotheses, contact orders, and exact subset threshold of the parent resultant-certificate frontier. There is a positive constant $C$ such that every admissible subset has the following data in its elliptic contact quotient, with $x$ denoting the elliptic coordinate.
--
--   Choose an element $y$, a polynomial $F$ of positive degree in $Y$, and a finite family $H_0,\ldots,H_{k-1}$ satisfying
--   $$F(x,y)=0,\qquad H_j(x,y)=0\quad(0\le j<k).$$
--   The equations hold in the contact quotient and therefore retain its derivative multiplicities. Every coefficient of $F$ has degree at most $a$ in $X$; each $H_j$ has degree at most $s$ in $Y$ and coefficient degrees at most $b$ in $X$.
--
--   After embedding $\mathbb C[X]$ into an algebraic closure of $\mathbb C(X)$, every root of $F$ is avoided by some $H_j$. Finally,
--   $$2\big((\deg_Y F)b+sa\big)+U+1\le Cn^2.$$
--   Constructing such bounded families remains the geometric task. The completed selection lemma turns any such family into the two relations required by the parent, without increasing the degree cost.
-- source:
--   Derived bounded-selection step for https://prove2.me/theorems/e228afdd-f183-4b04-ba4d-f76d7e7f01da. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. The selection lemma is a derived algebraic tool, not a claim to complete the paper zero estimate. Primary Lean sources: Mathlib Algebra/Polynomial/Roots.lean (root counts), RingTheory/Polynomial/Resultant/Basic.lean (product formula and Bezout identity), and Algebra/Polynomial/Degree/Operations.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. A finite family avoiding the roots of the first relation gives one resultant certificate with no increase in either polynomial degree bound.

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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

theorem WeierstrassEllipticZeta.bounded_subset_resultant_families (G : Frontier.Geometry) :
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
              let L := AlgebraicClosure (FractionRing (Polynomial ℂ))
              let φ : Polynomial ℂ →+* L :=
                (algebraMap (FractionRing (Polynomial ℂ)) L).comp
                  (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
              ∃ (y : MvPolynomial (Fin 4) ℂ ⧸ I)
                (F : Polynomial (Polynomial ℂ)) (k : ℕ)
                (H : Fin k → Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                (∀ j i, ((H j).coeff i).natDegree ≤ b) ∧
                (∀ j, (H j).natDegree ≤ s) ∧
                (∀ z ∈ (F.map φ).roots, ∃ j, (H j).eval₂ φ z ≠ 0) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧
                (∀ j, (H j).eval₂ (Polynomial.aeval x).toRingHom y = 0) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
