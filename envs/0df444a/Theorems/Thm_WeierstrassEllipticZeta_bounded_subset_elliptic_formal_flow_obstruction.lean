-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_elliptic_formal_flow_obstruction
-- name    : WeierstrassEllipticZeta.bounded_subset_elliptic_formal_flow_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T18:31:53.14727+00:00
-- url     : https://prove2.me/theorems/c0d95ff7-a3d1-4c4c-b453-ad81e88f6f79
-- title:
--   Coefficient obstruction for the explicit elliptic formal flow
-- statement:
--   Retain all geometric hypotheses of the parent, the selected subset, the contact ideal, the relation F(x,y)=0, and every numerical bound. At each point r of Z, allow any four formal power series J_{r,0},…,J_{r,3} with initial coefficients given by the chart-0 coordinates and satisfying
--
--   J_0'=1, J_1'=J_2, J_2'=6J_1²−g₂/2, J_3'=−J_1.
--
--   Choose p,F,a,b,s as in the parent and rule out the same finite coefficient interpolation weights at every root of F. The new quantification ranges over every family satisfying these explicit equations. Existence and uniqueness of the formal solution prove that this formulation is equivalent to the parent's canonical derivation-jet formulation, with identical C, subset threshold, degree bounds, and weights. The geometric exclusion of that coefficient interpolation system remains open.
-- source:
--   Derived formal ODE step for https://prove2.me/theorems/8bca4fbc-160b-4113-a9a7-68082ea63fd2. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a derived algebraic tool for the formal development, not a completion of the zero estimate. Uses the accepted theorem https://prove2.me/theorems/5ce4133e-3103-4283-a93b-f003cd47f11e. Primary Lean sources: Mathlib RingTheory/PowerSeries/Derivative.lean, RingTheory/PowerSeries/Basic.lean and Algebra/MvPolynomial/Derivation.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. Canonical derivation jets solve the polynomial ODE, and coefficient induction proves uniqueness. The explicit chart-0 equations and initial values therefore determine exactly the formal series in the parent obstruction.

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.PowerSeries.Basic
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

theorem WeierstrassEllipticZeta.bounded_subset_elliptic_formal_flow_obstruction (G : Frontier.Geometry) :
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
              ∀ J : Z → Fin 4 → PowerSeries ℂ,
                (∀ r a, PowerSeries.coeff 0 (J r a) =
                  extensionChartCoordinates G.S 0 r.val a) →
                (∀ r,
                  PowerSeries.derivative ℂ (J r 0) = 1 ∧
                  PowerSeries.derivative ℂ (J r 1) = J r 2 ∧
                  PowerSeries.derivative ℂ (J r 2) =
                    PowerSeries.C 6 * (J r 1) ^ 2 - PowerSeries.C (G.L.g₂ / 2) ∧
                  PowerSeries.derivative ℂ (J r 3) = -J r 1) →
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I p) = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  ¬ ∃ w : Z × Fin N → L, ∀ i ≤ s, ∀ j ≤ b,
                    (∑ r : Z × Fin N,
                      PowerSeries.coeff r.2.val
                        ((J r.1 (1 : Fin 4)) ^ j * (MvPolynomial.aeval (J r.1) p) ^ i) • w r) =
                      (φ Polynomial.X) ^ j * z ^ i) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
