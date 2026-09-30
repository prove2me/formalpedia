-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_period_contact_obstruction
-- name    : WeierstrassEllipticZeta.bounded_subset_period_contact_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-13T23:04:34.46623+00:00
-- url     : https://prove2.me/theorems/1cf89501-706f-4434-bf47-ac8f0a87de52
-- title:
--   Period bounds on subsets of prescribed cardinality
-- statement:
--   Retain all hypotheses of time_coordinate_cardinality_contact_obstruction, including the same ambient point set X, its local multiplicities, and its chart certificates. Prove that some positive constant C has the following property: whenever Y⊆X contains zero and
--
--   $$|Y|=\left\lfloor\frac{Cm n^2}{U+1}\right\rfloor+1,$$
--
--   its period-class count satisfies
--
--   $$ (U+1)|Y/\Omega|\le Cn^2. $$
--
--   This is an equivalent numerical formulation of the parent frontier, for the same constant. It bounds only these subsets of prescribed size; the geometric and analytic assumptions remain on X. No claim is made that the chart certificates automatically restrict to Y. The uniform geometric estimate and the main theorem remain open.
-- source:
--   Derived finite-subset reduction for the open frontier https://prove2.me/theorems/e074d90d-6a5f-46c1-9e9e-f986ff91e6bf. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3, https://doi.org/10.1017/S001309152610145X. The article motivates multiplicity-weighted counts of points and subgroup cosets; the subset selection theorem here is an independent elementary reduction, not a quotation or a proof of the article zero estimate. Primary formal sources are Mathlib Data/Set/Function.lean, Data/Finset/Card.lean, Data/Set/Card.lean and Algebra/Order/Floor/Semiring.lean at revision 0df444a360eaa60ab8c11dca51a86af692955474. The remaining statement is equivalent to the parent for the same constant and unchanged ambient hypotheses. The global estimate and main theorem remain open.

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.bounded_subset_period_contact_obstruction (G : Frontier.Geometry) :
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
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (Y : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2 := by sorry
