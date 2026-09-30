-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_time_coordinate_cardinality_contact_obstruction
-- name    : WeierstrassEllipticZeta.time_coordinate_cardinality_contact_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-13T22:38:18.711934+00:00
-- url     : https://prove2.me/theorems/e074d90d-6a5f-46c1-9e9e-f986ff91e6bf
-- title:
--   The time-coordinate cardinality or period obstruction
-- statement:
--   Under exactly the compact geometric and analytic hypotheses of weighted_face_boundary_jet_contact_obstruction, prove that a positive constant C gives the following alternative for every admissible m, n, U, X and Q: either (U+1)|X| ≤ C m n², or (U+1) times the number of period classes represented by X is at most C n².
--
--   This is the remaining uniform geometric estimate. It does not assume coordinatewise recurrences, separate coordinate-value counts, or a choice among derivatives of the normalized polynomial. The present contribution proves that this numerical alternative is sufficient for the weighted-face frontier; it does not prove the alternative or claim an equivalence with that frontier.
-- source:
--   Derived time-axis interpolation construction for the frontier https://prove2.me/theorems/1cce73f4-b850-4bca-a245-16357d88ad77. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, especially the time coordinate of the analytic subgroup and the numerical zero estimate Theorem A.3, https://doi.org/10.1017/S001309152610145X. This certificate is a derived construction using the already proved bounded Hermite interpolation theorem (20ad754f-4a6a-45a2-a323-9c692a5f3f83), not a quotation from the article. The remaining numerical alternative is an open sufficient condition for this frontier; no equivalence or completed global zero estimate is claimed. Lean/Mathlib environment: 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.time_coordinate_cardinality_contact_obstruction (G : Frontier.Geometry) :
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
            (((((U : ℕ) + 1) * X.card : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by sorry
