-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_jet_interpolation_obstruction
-- name    : WeierstrassEllipticZeta.bounded_subset_jet_interpolation_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T17:10:58.405575+00:00
-- url     : https://prove2.me/theorems/69db451e-8f1e-466d-8647-98d2545c7cb3
-- title:
--   Obstruction to finite jet interpolation of bounded monomials
-- statement:
--   Under the parent's exact geometry, local-order, degree, chart-certificate, and subset hypotheses, choose a polynomial representative p for the second quotient coordinate y and the same F,a,b,s satisfying F(x,y)=0 and the same numerical cost. For every root z of F over the algebraic closure of C(X), show that there is no array of target-field weights on Z×{0,…,N−1} whose weighted chart jets send every monomial X₁^j p^i, for 0≤i≤s and 0≤j≤b, to X^j z^i.
--
--   This is the finite system underlying the previous obstruction to a linear map on the contact quotient. The accompanying complete theorem converts maps into weights and weights into maps. A separate Lean converse lifts an arbitrary quotient coordinate to a polynomial representative, proving equivalence with the exact parent using the same constant, degree bounds, and subset threshold. Establishing the obstruction from the geometric hypotheses remains open.
-- source:
--   Derived finite-jet representation step for https://prove2.me/theorems/2fc7a002-4ac8-40ce-af14-a8aebb8fae9f. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a derived linear-algebra tool for the formal development, not a completion of the zero estimate. Primary Lean sources: Mathlib LinearAlgebra/Basis/VectorSpace.lean, LinearAlgebra/Isomorphisms.lean and LinearAlgebra/Pi.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The stable geometry contact-ideal membership axiom identifies the kernel of the finite jet map. Embedding the contact quotient into the jet-coordinate space and extending a linear map gives a finite weighted-jet representation; every weight array defines a unique quotient map.

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

theorem WeierstrassEllipticZeta.bounded_subset_jet_interpolation_obstruction (G : Frontier.Geometry) :
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
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I p) = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  ¬ ∃ w : Z × Fin N → L, ∀ i ≤ s, ∀ j ≤ b,
                    (∑ r : Z × Fin N,
                      MvPolynomial.eval (extensionChartCoordinates G.S 0 r.1.val)
                        ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[r.2.val]
                          ((MvPolynomial.X (1 : Fin 4)) ^ j * p ^ i)) • w r) =
                      (φ Polynomial.X) ^ j * z ^ i) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
