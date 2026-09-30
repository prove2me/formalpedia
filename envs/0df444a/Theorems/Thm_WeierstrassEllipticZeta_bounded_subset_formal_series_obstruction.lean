-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_formal_series_obstruction
-- name    : WeierstrassEllipticZeta.bounded_subset_formal_series_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T17:31:52.962607+00:00
-- url     : https://prove2.me/theorems/8bca4fbc-160b-4113-a9a7-68082ea63fd2
-- title:
--   Obstruction to finite coefficient interpolation of formal series
-- statement:
--   Keep the parent's exact geometric hypotheses, chosen subset, contact order and ideal, relation F(x,y)=0, and all numerical bounds. At each contact point form four formal coordinate series by dividing the k-th chart derivation jet of each coordinate by k!. Choose the same polynomial representative p and F,a,b,s. At every root z of F over the algebraic closure of C(X), rule out weights on the first N coefficients at all contact points whose weighted values on J₁^j p(J)^i equal X^j z^i throughout 0≤i≤s, 0≤j≤b.
--
--   The complete formal substitution theorem identifies the coefficients with the original jets after multiplication by k!. A separate Lean converse rescales each weight by the inverse factorial, checking exact equivalence with the parent and preserving the same C, degree bounds, and subset threshold. These are formal power series; no analytic convergence is assumed or asserted. Excluding the finite coefficient interpolation system from the geometric hypotheses remains open.
-- source:
--   Derived formal Taylor substitution step for https://prove2.me/theorems/69db451e-8f1e-466d-8647-98d2545c7cb3. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the formal development, not a completion of the zero estimate. Primary Lean sources: Mathlib RingTheory/Derivation/Basic.lean, Data/Nat/Choose/Sum.lean, Data/Nat/Choose/Cast.lean and RingTheory/PowerSeries/Basic.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The iterated Leibniz rule and factorial normalization identify polynomial substitution into the coordinate formal series with all iterated derivation jets. Invertible factorial rescaling preserves the finite interpolation obstruction exactly.

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

theorem WeierstrassEllipticZeta.bounded_subset_formal_series_obstruction (G : Frontier.Geometry) :
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
              let J : Z → Fin 4 → PowerSeries ℂ := fun r a => PowerSeries.mk fun k =>
                MvPolynomial.eval (extensionChartCoordinates G.S 0 r.val)
                  ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[k]
                    (MvPolynomial.X a)) / (k.factorial : ℂ)
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
