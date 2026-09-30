-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_rootwise_relations
-- name    : WeierstrassEllipticZeta.bounded_subset_rootwise_relations
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T16:19:01.321763+00:00
-- url     : https://prove2.me/theorems/220d1ce8-77e0-4688-b5f4-240f40909f00
-- title:
--   A bounded contact relation avoiding each root separately
-- statement:
--   Retain every geometric, auxiliary-polynomial, contact-order, and subset hypothesis of the parent bounded-family frontier. There is a positive uniform constant $C$ such that every admissible subset has the following data in its elliptic contact quotient, with elliptic coordinate $x$.
--
--   Choose an element $y$, a bivariate polynomial $F$ of positive degree in $Y$, and nonnegative integers $a,b,s$ such that
--   $$F(x,y)=0,\qquad \deg_X F_i\le a\quad\text{for every coefficient }F_i,$$
--   and
--   $$2\big((\deg_Y F)b+sa\big)+U+1\le Cn^2.$$
--   For each root $z$ of $F$ over the fixed algebraic closure of $\mathbb C(X)$, there exists a polynomial $P_z$ satisfying
--   $$\deg_Y P_z\le s,\qquad \deg_X(P_z)_i\le b,\qquad P_z(x,y)=0,\qquad P_z(z)\ne0.$$
--   Here the last evaluation applies the coefficient embedding into that algebraic closure. The relation equation holds in the contact quotient, so it preserves derivative multiplicities. The witness polynomial may depend on the root. The completed basis theorem assembles all these witnesses into a single finite family with the same degree bounds; finding the witnesses remains open.
-- source:
--   Derived bounded relation-space step for https://prove2.me/theorems/08ae25ab-c63e-48d2-ab17-5189a85148d9. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This basis construction is a derived algebraic tool, not a claim to complete the paper zero estimate. Primary Lean sources: Mathlib Algebra/Polynomial/AlgebraMap.lean, Algebra/Polynomial/Degree/Defs.lean, LinearAlgebra/FiniteDimensional/Basic.lean, LinearAlgebra/Dimension/Free.lean, and LinearAlgebra/Span/Basic.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The kernel of bounded bivariate evaluation has a basis no larger than the coefficient rectangle. It assembles individual root-avoiding witnesses into a finite family with unchanged bounds.

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

theorem WeierstrassEllipticZeta.bounded_subset_rootwise_relations (G : Frontier.Geometry) :
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
                (∀ z ∈ (F.map φ).roots, ∃ P : Polynomial (Polynomial ℂ),
                  P.natDegree ≤ s ∧ (∀ i, (P.coeff i).natDegree ≤ b) ∧
                    P.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧ P.eval₂ φ z ≠ 0) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
