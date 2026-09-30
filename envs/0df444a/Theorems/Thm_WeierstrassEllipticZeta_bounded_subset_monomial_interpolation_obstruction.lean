-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_monomial_interpolation_obstruction
-- name    : WeierstrassEllipticZeta.bounded_subset_monomial_interpolation_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T16:43:41.18204+00:00
-- url     : https://prove2.me/theorems/2fc7a002-4ac8-40ce-af14-a8aebb8fae9f
-- title:
--   Obstruction to bounded monomial interpolation on a contact quotient
-- statement:
--   Under exactly the parent geometry, chart, order, degree, and subset hypotheses, choose y,F,a,b,s with the same positive outer degree, relation F(x,y)=0, coefficient-degree bound, and final numerical cost. For each root z of F over the algebraic closure of C(X), show that no C-linear map from the contact quotient to that field sends x^j y^i to X^j z^i throughout the rectangle 0≤i≤s, 0≤j≤b.
--
--   The target field has its canonical complex algebra structure. This is an obstruction to a linear interpolation problem on a finite monomial family; multiplicativity is not required. A separate Lean converse checks that this condition is equivalent to the parent's bounded root-avoiding relation condition with the same uniform constant C. Establishing this obstruction from the geometric hypotheses remains open.
-- source:
--   Derived linear separation step for https://prove2.me/theorems/220d1ce8-77e0-4688-b5f4-240f40909f00. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a derived algebraic tool, not a completion of the paper zero estimate. Primary Lean sources: Mathlib Algebra/Polynomial/AlgebraMap.lean, LinearAlgebra/Basis/VectorSpace.lean and LinearAlgebra/Isomorphisms.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. Bounded polynomial separation is equivalent to failure to interpolate the corresponding bounded monomials by a linear map. The first isomorphism theorem and extension of linear maps prove the difficult implication, preserving every degree bound.

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

theorem WeierstrassEllipticZeta.bounded_subset_monomial_interpolation_obstruction (G : Frontier.Geometry) :
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
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  ¬ ∃ T : (MvPolynomial (Fin 4) ℂ ⧸ I) →ₗ[ℂ] L,
                    ∀ i ≤ s, ∀ j ≤ b, T (x ^ j * y ^ i) = (φ Polynomial.X) ^ j * z ^ i) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
