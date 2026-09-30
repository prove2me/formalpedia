-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_finite_rank_obstruction
-- name    : WeierstrassEllipticZeta.bounded_subset_finite_rank_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-19T17:53:43.081513+00:00
-- url     : https://prove2.me/theorems/37582c08-3ae4-434c-b78d-a8083d516763
-- title:
--   Finite matrix ranks for elliptic interpolation obstructions
-- statement:
--   Retain all hypotheses and data of the [sparse interpolation frontier](https://prove2.me/theorems/4af1c4a0-3334-49b6-b559-e122c13d1774). In particular retain the same geometry, finite subset, contact quotient, formal flows, reduced representatives, common denominator, and numerator polynomials. Put $I=Z\times\{0,\ldots,N-1\}$, $d=2N|Z|$, and $t=\varphi(T)$; write $W$ for the generating variable and a bar for extension of coefficients to $L$.
--
--   The assertion supplies the same witnesses $p,F,a,b,s$, the same nonconstant relation $F$ in the contact quotient, and the same estimate
--
--   $$2(\deg(F)b+sa)+(U+1)\le Cn^2.$$
--
--   For each root $z$ covered by the original chart-spectrum applicability condition, require these finite matrix rank inequalities.
--
--   If $s<d$, use rows $(j,h)$ with $0\le j\le b$ and $0\le h\le s$. Define an $I$-column matrix $\mathcal A$ and a one-column matrix $\mathcal B$ over $L$ by
--
--   $$\mathcal A_{(j,h),i}=[W^h]\big((1-zW)\overline{V_{p,i,j}}(W)\big),\qquad
--   \mathcal B_{(j,h),*}=[W^h]\big(t^j\overline{\Omega_p}(W)\big).$$
--
--   If $d\le s$, for each $c\in\mathbb C$ whose image in $L$ equals $z$, use rows $(j,h)$ with $0\le j\le b$ and $0\le h\le d$. Define matrices over $\mathbb C$ by
--
--   $$\mathcal A_{(j,h),i}=[W^h]\big((1-cW)V_{p,i,j}(W)\big),\qquad
--   \mathcal B_{(j,h),k}=[W^h]\big(\delta_{kj}\Omega_p(W)\big),\quad 0\le k\le b.$$
--
--   In either case require
--
--   $$\operatorname{rank}\mathcal A<\operatorname{rank}[\mathcal A\mid\mathcal B].$$
--
--   Both matrices are finite: the short branch has $(b+1)(s+1)$ rows; the exact branch has $(b+1)(d+1)$ rows. The assertion contains no certificate multipliers or unbounded coefficient indices. It is equivalent to the parent obstruction and incurs no loss in the constant or cost. Obtaining the witnesses with this geometric estimate remains the open problem.
-- source:
--   Derived finite coefficient rank criterion for the interpolation frontier https://prove2.me/theorems/4af1c4a0-3334-49b6-b559-e122c13d1774. Primary sources: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, LinearAlgebra/Matrix/Rank.lean, Matrix.rank_eq_finrank_span_cols, line 398: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Rank.lean#L398; LinearAlgebra/FiniteDimensional/Lemmas.lean, Submodule.finrank_lt_finrank_of_lt, line 235: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean#L235; Algebra/Polynomial/Degree/Operations.lean, Polynomial.coeff_eq_zero_of_natDegree_lt, line 85: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Degree/Operations.lean#L85. The complete theorem is derived here from finite-dimensional column spans and coefficient vanishing above degree; it is not a verbatim theorem from the mission paper. Mission context: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The connecting reduction preserves all hypotheses, witnesses, root conditions and numerical bounds, while bounding the exact branch coefficient indices by 2N|Z| and adjoining every right-hand-side column simultaneously. Both directions are checked in Lean. The uniform geometric estimate remains open.

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

theorem WeierstrassEllipticZeta.bounded_subset_finite_rank_obstruction (G : Frontier.Geometry) :
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
                    let Ac : Matrix (Fin (b + 1) × Fin (s + 1)) (Z × Fin N) L :=
                      fun e q => ((1 - Polynomial.C z * Polynomial.X) *
                        (V p q.1 e.1.val q.2).map (algebraMap ℂ L)).coeff e.2.val
                    let Bc : Matrix (Fin (b + 1) × Fin (s + 1)) Unit L :=
                      fun e _ => (Polynomial.C ((φ Polynomial.X) ^ e.1.val) *
                        (Ω p).map (algebraMap ℂ L)).coeff e.2.val
                    Ac.rank < (Matrix.fromCols Ac Bc).rank
                  else
                    ∀ c : ℂ, z = algebraMap ℂ L c →
                      let Ac : Matrix (Fin (b + 1) × Fin (2 * N * Z.card + 1))
                          (Z × Fin N) ℂ := fun e q =>
                        ((1 - Polynomial.C c * Polynomial.X) *
                          V p q.1 e.1.val q.2).coeff e.2.val
                      let Bc : Matrix (Fin (b + 1) × Fin (2 * N * Z.card + 1))
                          (Fin (b + 1)) ℂ := fun e k =>
                        (if k.val = e.1.val then Ω p else 0).coeff e.2.val
                      Ac.rank < (Matrix.fromCols Ac Bc).rank) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by sorry
