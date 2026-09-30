-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_common_denominator_obstruction
-- name    : WeierstrassEllipticZeta.bounded_subset_common_denominator_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T22:10:35.981067+00:00
-- url     : https://prove2.me/theorems/c76b8017-d835-48d3-8f68-1d93aea9503a
-- title:
--   Interpolation obstruction with one common denominator
-- statement:
--   Retain the hypotheses and data of the [bounded jet-numerator frontier](https://prove2.me/theorems/1555b7ac-bf6a-43b2-974d-ea1798d3c73b). In particular, C is its positive uniform constant, m,n,U are the integer parameters, Y is the tested finite subset, Z consists of its points outside the lattice, and N=3U+1 is the contact order. The auxiliary polynomial, local vanishing orders, derivative degree bounds, chart certificates, contact quotient and local formal series satisfy all the parent's assumptions.
--
--   For every polynomial p in four variables, the parent supplies quadratic polynomials qₚᵣ with constant coefficient one, formal inverses H₀,ₚᵣ, and local numerator polynomials Mₚᵣⱼₖ of degree at most 2k+1. Set
--
--   $$\Omega_p(z)=\prod_{r\in Z}q_{pr}(z)^N,\qquad
--   H_{1,p}(z)=\prod_{r\in Z}H_{0,pr}(z)^N.$$
--
--   Assume the certificates
--
--   $$\deg\Omega_p\le 2N|Z|,\qquad \Omega_pH_{1,p}=1.$$
--
--   Let V be any family of complex polynomials, indexed by p,r, a nonnegative integer j and 0≤k<N, satisfying
--
--   $$\deg V_{prjk}<2N|Z|,\qquad
--   M_{prjk}H_{0,pr}^{k+1}=V_{prjk}H_{1,p}.$$
--
--   The assertion is that the same uniform C permits p, a nonconstant polynomial F with polynomial coefficients, and nonnegative integers a,b,s satisfying the parent's coefficient degree bound, contact-quotient relation and cost bound
--
--   $$2(\deg(F)b+sa)+(U+1)\le Cn^2,$$
--
--   such that, for every root λ of F in the parent's scalar extension, no family of weights wᵣₖ in that algebraic closure satisfies
--
--   $$\sum_{r\in Z}\sum_{k<N}[z^i]\bigl(V_{prjk}(z)H_{1,p}(z)\bigr)w_{rk}
--   =t^j\lambda^i\qquad(0\le i\le s,\ 0\le j\le b).$$
--
--   Here t is the image of the polynomial variable under the parent's scalar-extension map. The assertion retains every previous hypothesis and is required for every admissible numerator family V. It imposes no new lower bound on s.
--
--   All terms now share one denominator, independent of r,j,k for a fixed p. The remaining task is the geometric exclusion of the displayed finite interpolation system.
-- source:
--   Derived common-denominator step for https://prove2.me/theorems/1555b7ac-bf6a-43b2-974d-ea1798d3c73b. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib Algebra/Polynomial/BigOperators.lean (natDegree_prod_le), Degree/Defs.lean (product and power degree bounds), Algebra/BigOperators/Group/Finset/Basic.lean (mul_prod_erase), and RingTheory/PowerSeries/Basic.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. See https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/BigOperators.html. Multiply each numerator by the missing denominator factors. The common product has degree at most d*N*card(I), and the new numerators have degree strictly below that uniform bound. The mission application uses d=2 and preserves every interpolation witness, weight and numerical bound.

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

theorem WeierstrassEllipticZeta.bounded_subset_common_denominator_obstruction (G : Frontier.Geometry) :
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
                  ¬ ∃ w : Z × Fin N → L, ∀ i ≤ s, ∀ j ≤ b,
                    (∑ r : Z × Fin N,
                      PowerSeries.coeff i
                        ((V p r.1 j r.2 : PowerSeries ℂ) * H₁ p) • w r) =
                      (φ Polynomial.X) ^ j * z ^ i) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
