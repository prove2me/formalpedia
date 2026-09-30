-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_scalar_interpolation_obstruction
-- name    : WeierstrassEllipticZeta.bounded_subset_scalar_interpolation_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-19T16:30:54.336813+00:00
-- url     : https://prove2.me/theorems/0fa8049d-86af-4361-abe7-f37ded0bf6d0
-- title:
--   Elliptic interpolation obstruction through scalar systems
-- statement:
--   Retain every hypothesis and all the data of the [explicit chart-spectrum frontier](https://prove2.me/theorems/6b3b6a47-f0a5-48cd-8609-9cab71006042). In particular, retain the uniform positive constant $C$, the tested subset $Y$, its nonlattice part $Z$, the order $N=3U+1$, the contact quotient, formal series, polynomial representatives, and denominator certificates. Put $d=2N|Z|$.
--
--   The assertion supplies the same witnesses $p,F,a,b,s$, with the same nonconstant relation $F$, bounds on its coefficients, relation in the contact quotient, and numerical cost
--
--   $$2(\deg(F)b+sa)+(U+1)\le Cn^2.$$
--
--   At every root $\lambda$ of the scalar-extended relation, retain the same applicability condition: either $s<d$, or $\lambda$ is the value of $p$ at one of the chart points or its reflection in the derivative coordinate.
--
--   When $s<d$, retain the original exclusion of weights satisfying all the congruences modulo the $(s+1)$st power of the generating variable.
--
--   When $d\le s$, replace the extension-field exclusion as follows. For every $c\in\mathbb C$ whose image in the extension field is $\lambda$, there is an integer $k$ with $0\le k\le b$ such that no single family $u:Z\times\{0,\ldots,N-1\}\to\mathbb C$ satisfies, simultaneously for all $0\le j\le b$,
--
--   $$(1-cT)\sum_{(r,e)}u_{r,e}V_{p,r,j,e}(T)=\delta_{kj}\Omega_p(T).$$
--
--   Here $V$ and $\Omega$ are exactly the numerator and common-denominator polynomials supplied in the parent. Only the weights and right-hand sides in the exact-identity case change. The chart-value condition ensures that a scalar $c$ exists in that case.
--
--   This is an equivalent formulation of the parent frontier. It reduces its exact interpolation condition to failure of one of $b+1$ systems over $\mathbb C$, each having $N|Z|$ unknown scalar weights. The uniform geometric estimate needed to produce the witnesses remains open.
-- source:
--   Derived linear-algebra reduction of the exact-interpolation clause in https://prove2.me/theorems/6b3b6a47-f0a5-48cd-8609-9cab71006042. The primary linear-algebra input is Mathlib, revision 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/LinearAlgebra/Basis/VectorSpace.lean, LinearMap.exists_leftInverse_of_injective (lines 240 onward): https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Basis/VectorSpace.lean#L240. Polynomial coefficient and scalar-extension APIs: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/AlgebraMap.lean. The displayed descent equivalence is a derived lemma, not a quotation from the mission paper. Mission context: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The parent is preserved outside its exact-interpolation exclusion clause; the same hypotheses, root applicability condition, witnesses and numerical bound are retained. Separate Lean proofs check both directions. The uniform geometric estimate remains open.

import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.ComputeDegree
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Choose
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

theorem WeierstrassEllipticZeta.bounded_subset_scalar_interpolation_obstruction (G : Frontier.Geometry) :
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
              (Ideal.span ({extensionChartCubic G.L.g₂ G.L.g₃ 0} :
                Set (MvPolynomial (Fin 4) ℂ)) ≤ I) →
              let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
              let L := AlgebraicClosure (FractionRing (Polynomial ℂ))
              let φ : Polynomial ℂ →+* L :=
                (algebraMap (FractionRing (Polynomial ℂ)) L).comp
                  (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
              let v : Z → Fin 4 → ℂ := fun r => extensionChartCoordinates G.S 0 r.val
              ∀ P : Z → PowerSeries ℂ,
                (∀ r, PowerSeries.coeff 0 (P r) = v r 1 ∧
                  PowerSeries.coeff 1 (P r) = v r 2) →
                (∀ r, PowerSeries.derivative ℂ (PowerSeries.derivative ℂ (P r)) =
                  PowerSeries.C 6 * (P r) ^ 2 - PowerSeries.C (G.L.g₂ / 2)) →
                (∀ r, (PowerSeries.derivative ℂ (P r)) ^ 2 =
                  PowerSeries.C 4 * (P r) ^ 3 - PowerSeries.C G.L.g₂ * P r -
                    PowerSeries.C G.L.g₃) →
              let J : Z → Fin 4 → PowerSeries ℂ := fun r =>
                ![PowerSeries.C (v r 0) + PowerSeries.X, P r, PowerSeries.derivative ℂ (P r),
                  PowerSeries.mk fun k =>
                    if k = 0 then v r 3 else -PowerSeries.coeff (k - 1) (P r) / (k : ℂ)]
              ∀ ρ : MvPolynomial (Fin 4) ℂ → MvPolynomial (Fin 4) ℂ,
                (∀ p, (ρ p).degreeOf (2 : Fin 4) ≤ 1 ∧ p - ρ p ∈
                  Ideal.span ({extensionChartCubic G.L.g₂ G.L.g₃ 0} :
                    Set (MvPolynomial (Fin 4) ℂ))) →
              let D : Z → PowerSeries ℂ := fun r =>
                PowerSeries.C 4 * (P r) ^ 3 - PowerSeries.C G.L.g₂ * P r -
                  PowerSeries.C G.L.g₃
              let A : MvPolynomial (Fin 4) ℂ → Z → PowerSeries ℂ := fun p r =>
                MvPolynomial.aeval (Function.update (J r) (2 : Fin 4) 0) (ρ p)
              let B : MvPolynomial (Fin 4) ℂ → Z → PowerSeries ℂ := fun p r =>
                MvPolynomial.aeval (Function.update (J r) (2 : Fin 4) 0)
                  (MvPolynomial.pderiv (2 : Fin 4) (ρ p))
              let T : MvPolynomial (Fin 4) ℂ → Z → ℕ → PowerSeries ℂ × PowerSeries ℂ :=
                fun p r => Nat.rec (1, 0)
                  (fun _ t => (A p r * t.1 + D r * B p r * t.2,
                    B p r * t.1 + A p r * t.2))
              (∀ p r i, (T p r i).1 ^ 2 - D r * (T p r i).2 ^ 2 =
                (A p r ^ 2 - D r * B p r ^ 2) ^ i) →
              let H : MvPolynomial (Fin 4) ℂ → Z → PowerSeries (PowerSeries ℂ) := fun p r =>
                PowerSeries.invOfUnit
                  (1 - PowerSeries.C (2 * A p r) * PowerSeries.X +
                    PowerSeries.C (A p r ^ 2 - D r * B p r ^ 2) * PowerSeries.X ^ 2)
                  (1 : (PowerSeries ℂ)ˣ)
              ∀ τ : PowerSeries (PowerSeries ℂ) ≃+* PowerSeries (PowerSeries ℂ),
                (∀ (f : PowerSeries (PowerSeries ℂ)) (i k : ℕ),
                  PowerSeries.coeff i (PowerSeries.coeff k (τ f)) =
                    PowerSeries.coeff k (PowerSeries.coeff i f)) →
              let ψ : PowerSeries ℂ →+* PowerSeries (PowerSeries ℂ) :=
                PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ)
              let W : PowerSeries (PowerSeries ℂ) := PowerSeries.C (PowerSeries.X : PowerSeries ℂ)
              let K : MvPolynomial (Fin 4) ℂ → Z → PowerSeries (PowerSeries ℂ) := fun p r => τ (H p r)
              (∀ p r, (1 - ψ (2 * A p r) * W +
                ψ (A p r ^ 2 - D r * B p r ^ 2) * W ^ 2) * K p r = 1) →
              let E : MvPolynomial (Fin 4) ℂ → Z → ℕ → PowerSeries (PowerSeries ℂ) :=
                fun p r j => ψ ((J r (1 : Fin 4)) ^ j) *
                  ((1 - ψ (A p r) * W) * K p r +
                    ψ (J r (2 : Fin 4)) * (ψ (B p r) * W * K p r))
              let q : MvPolynomial (Fin 4) ℂ → Z → Polynomial ℂ := fun p r =>
                1 - Polynomial.C (PowerSeries.coeff 0 (2 * A p r)) * Polynomial.X +
                  Polynomial.C (PowerSeries.coeff 0 (A p r ^ 2 - D r * B p r ^ 2)) * Polynomial.X ^ 2
              let H₀ : MvPolynomial (Fin 4) ℂ → Z → PowerSeries ℂ := fun p r =>
                PowerSeries.invOfUnit (q p r : PowerSeries ℂ) (1 : ℂˣ)
              ∀ M : MvPolynomial (Fin 4) ℂ → Z → ℕ → ℕ → Polynomial ℂ,
                (∀ p r j k, (M p r j k).natDegree ≤ 2 * k + 1 ∧
                  PowerSeries.coeff k (E p r j) =
                    (M p r j k : PowerSeries ℂ) * H₀ p r ^ (k + 1)) →
              let Ω : MvPolynomial (Fin 4) ℂ → Polynomial ℂ := fun p => ∏ r : Z, q p r ^ N
              let H₁ : MvPolynomial (Fin 4) ℂ → PowerSeries ℂ := fun p => ∏ r : Z, H₀ p r ^ N
              (∀ p, (Ω p).natDegree ≤ 2 * N * Z.card ∧ (Ω p : PowerSeries ℂ) * H₁ p = 1) →
              ∀ V : MvPolynomial (Fin 4) ℂ → Z → ℕ → Fin N → Polynomial ℂ,
                (∀ p r j k, (V p r j k).natDegree < 2 * N * Z.card ∧
                  (M p r j k.val : PowerSeries ℂ) * H₀ p r ^ (k.val + 1) =
                    (V p r j k : PowerSeries ℂ) * H₁ p) →
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I (ρ p)) = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  (s < 2 * N * Z.card ∨ ∃ r : Z,
                    z = algebraMap ℂ L (MvPolynomial.aeval (v r) p) ∨
                      z = algebraMap ℂ L
                        (MvPolynomial.aeval
                          (Function.update (v r) (2 : Fin 4) (-v r 2)) p)) →
                  if s < 2 * N * Z.card then
                    ¬ ∃ w : Z × Fin N → L, ∀ j ≤ b,
                      Polynomial.X ^ (s + 1) ∣
                        (1 - Polynomial.C z * Polynomial.X) *
                          (∑ r : Z × Fin N, Polynomial.C (w r) *
                            (V p r.1 j r.2).map (algebraMap ℂ L)) -
                          Polynomial.C ((φ Polynomial.X) ^ j) *
                            (Ω p).map (algebraMap ℂ L)
                  else
                    ∀ c : ℂ, z = algebraMap ℂ L c →
                      ∃ k ≤ b, ¬ ∃ u : Z × Fin N → ℂ, ∀ j ≤ b,
                        (1 - Polynomial.C c * Polynomial.X) *
                          (∑ r : Z × Fin N, Polynomial.C (u r) * V p r.1 j r.2) =
                            if k = j then Ω p else 0) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
