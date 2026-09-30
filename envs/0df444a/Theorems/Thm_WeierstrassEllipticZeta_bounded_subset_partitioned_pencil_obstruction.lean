-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_partitioned_pencil_obstruction
-- name    : WeierstrassEllipticZeta.bounded_subset_partitioned_pencil_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-20T02:04:30.241441+00:00
-- url     : https://prove2.me/theorems/e515f1b6-6149-4f08-bd4c-64b27d108fd8
-- title:
--   Partitioned integer bounds for elliptic pencil certificates
-- statement:
--   Retain all hypotheses of the [bounded polynomial pencil frontier](https://prove2.me/theorems/d34f0ebd-9300-4a3a-8ed1-ebee75d0d32c), including its geometric, contact-quotient, formal-series, common-denominator, and valid-detector data. Write N=3U+1 and d_*=2N|Z|, where Z is the finite set of nonlattice chart points.
--
--   Construct the same p,F,a,b,s, with F in C[T][Y], positive degree e in Y, coefficient degrees in T at most a, and the original relation and bound
--
--   $$F(x,\rho(p))=0,\qquad 2(eb+sa)+(U+1)\le Cn^2.$$
--
--   The short branch s<d_* retains the existing bounded certificate over the algebraic closure of Frac(C[T]). Its hypotheses, coefficient bounds and identity are unchanged.
--
--   For the long branch s>=d_*, index the two chart values at each point by I=Z+Z. On the first copy set c_i=alpha_r, the value of p at the chart point. On the second copy set c_i=beta_r, the value after negating only the derivative coordinate. Put
--
--   $$z=|\{i\in I:D_l(p,b)(c_i)=0\}|,\qquad
--   q=|\{i\in I:D_l(p,b)(c_i)\ne0\}|.$$
--
--   Thus z+q=2|Z|; entries are counted with their indices, including repeated values. Require nonnegative integers
--
--   $$0\le t\le za,\qquad 0\le k\le q.$$
--
--   With F_t(Y)=F(t,Y) and H_{t,k}(Y)=F_t(Y)+kD_l(p,b)(Y), require the same nonzero complex product
--
--   $$\prod_{r\in Z}H_{t,k}(\alpha_r)H_{t,k}(\beta_r)\ne0.$$
--
--   Only the two integer ranges change. The original polynomial F remains in the quotient relation, degree and coefficient bounds, and cost estimate. A complete algebraic equivalence shows that these smaller ranges impose no extra geometric requirement. Constructing p,F,a,b,s and establishing the geometric estimate remain open.
-- source:
--   Derived refinement of bounded simultaneous specialization and bounded finite linear-combination nonvanishing, and equivalent reduction of https://prove2.me/theorems/d34f0ebd-9300-4a3a-8ed1-ebee75d0d32c. Reuses complete platform theorems bounded_bivariate_specialization (aa9fdd40-d30b-4f1e-aa4e-241e9f3bd925) and bounded_finite_pencil_nonvanishing (a4d2e3a6-7cf0-4761-9c5b-829b25bf7f3e). Primary Mathlib source at revision 0df444a360eaa60ab8c11dca51a86af692955474: Fintype.card_le_of_injective, line 240, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Fintype/Card.lean#L240. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This refinement is derived here, not a verbatim theorem from the paper.

import Mathlib.Data.Matrix.ColumnRowPartitioned
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

theorem WeierstrassEllipticZeta.bounded_subset_partitioned_pencil_obstruction (G : Frontier.Geometry) :
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
              ∀ Ds : MvPolynomial (Fin 4) ℂ → ℕ → ℕ → Polynomial L,
                (∀ p b s, (Ds p b s).natDegree ≤ s ∧ ∀ z : L,
                  let Ac : Matrix (Fin (b + 1) × Fin (s + 1)) (Z × Fin N) L :=
                    fun e q => ((V p q.1 e.1.val q.2).map (algebraMap ℂ L)).coeff e.2.val
                  let Rz : Polynomial L := ∑ k ∈ Finset.range (s + 1),
                    (Polynomial.C z * Polynomial.X) ^ k
                  let Bc : Matrix (Fin (b + 1) × Fin (s + 1)) Unit L :=
                    fun e _ => (Rz * (Polynomial.C ((φ Polynomial.X) ^ e.1.val) *
                      (Ω p).map (algebraMap ℂ L))).coeff e.2.val
                  (Ac.rank < (Matrix.fromCols Ac Bc).rank) ↔ (Ds p b s).eval z ≠ 0) →
              ∀ Dl : MvPolynomial (Fin 4) ℂ → ℕ → Polynomial ℂ,
                (∀ p b, (Dl p b).natDegree ≤ 2 * N * Z.card ∧ ∀ c : ℂ,
                  let Ac : Matrix (Fin (b + 1) × Fin (2 * N * Z.card + 1))
                      (Z × Fin N) ℂ := fun e q => (V p q.1 e.1.val q.2).coeff e.2.val
                  let Rc : Polynomial ℂ := ∑ k ∈ Finset.range (2 * N * Z.card + 1),
                    (Polynomial.C c * Polynomial.X) ^ k
                  let Bc : Matrix (Fin (b + 1) × Fin (2 * N * Z.card + 1))
                      (Fin (b + 1)) ℂ := fun e k =>
                    (Rc * (if k.val = e.1.val then Ω p else 0)).coeff e.2.val
                  (Ac.rank < (Matrix.fromCols Ac Bc).rank) ↔ (Dl p b).eval c ≠ 0) →
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I (ρ p)) = 0 ∧
                (if s < 2 * N * Z.card then
                  ∃ u w : Polynomial L,
                    u * F.map φ + w * Ds p b s = 1 ∧
                    w.natDegree < F.natDegree ∧ u.natDegree ≤ (Ds p b s).natDegree
                else
                  let c : Z ⊕ Z → ℂ := Sum.elim
                    (fun r => MvPolynomial.aeval (v r) p)
                    (fun r => MvPolynomial.aeval
                      (Function.update (v r) (2 : Fin 4) (-v r 2)) p)
                  ∃ t : Fin (Fintype.card {i : Z ⊕ Z // (Dl p b).eval (c i) = 0} * a + 1),
                    ∃ k : Fin (Fintype.card {i : Z ⊕ Z // (Dl p b).eval (c i) ≠ 0} + 1),
                      let Ft : Polynomial ℂ :=
                        F.map (Polynomial.evalRingHom (t.val : ℂ))
                      let Ht : Polynomial ℂ := Ft + Polynomial.C (k.val : ℂ) * Dl p b
                      (∏ r : Z,
                        Ht.eval (MvPolynomial.aeval (v r) p) *
                          Ht.eval (MvPolynomial.aeval
                            (Function.update (v r) (2 : Fin 4) (-v r 2)) p)) ≠ 0) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
