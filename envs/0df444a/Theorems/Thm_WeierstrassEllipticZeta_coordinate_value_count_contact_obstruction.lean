-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_coordinate_value_count_contact_obstruction
-- name    : WeierstrassEllipticZeta.coordinate_value_count_contact_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-13T20:48:38.211485+00:00
-- url     : https://prove2.me/theorems/7474c39b-a6ed-4850-82c1-ddace253bc6b
-- title:
--   Coordinate-value counts and weighted contact face bounds
-- statement:
--   Under the same compact geometry, local order, degree, and chart-certificate hypotheses as `coordinate_recurrence_contact_obstruction`, obtain its period-class alternative or chart assignments, nonzero contact polynomials p_c and box bounds b_c satisfying the same degree-weighted face estimate and contact conditions, together with the following sufficient coordinate-value count bound.
--
--   For each chart c and coordinate i let T_ci be the set of distinct i-th coordinate values of the points assigned to that chart. Require
--
--   $$(U+1)|T_{ci}|\le b_{ci}+1.$$
--
--   This replaces the existential family of coordinate contact recurrences. The new count condition is sufficient to construct that family; equivalence to the existence of arbitrary coordinate recurrences is not claimed. Establishing these bounds with one positive uniform C, or the period-class alternative, is the remaining geometric obligation.
-- source:
--   Derived finite-coordinate-value sufficient criterion for the frontier https://prove2.me/theorems/719a9dcd-3d98-4eb4-a179-dc77f9aa6a0d. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The generic construction is derived using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Algebra/Polynomial/BigOperators.lean (natDegree_finsetProd_X_sub_C_eq_card), Algebra/Polynomial/Degree/IsMonicOfDegree.lean (exists_natDegree_lt), Algebra/MvPolynomial/Equiv.lean (toMvPolynomial, eval_toMvPolynomial), and RingTheory/Ideal/Operations.lean (pow_mem_pow). The uniform geometric estimate with the new sufficient coordinate-value count condition remains open; equivalence to arbitrary coordinate recurrences is not asserted.

import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.coordinate_value_count_contact_obstruction (G : Frontier.Geometry) :
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
            ((∃ a : X → Fin 2,
              (∀ x : X, G.S (extensionChartDenominator (a x)) x.val ≠ 0) ∧
              ∃ b : Fin 2 → (Fin 4 →₀ ℕ),
              ∃ p : Fin 2 → MvPolynomial (Fin 4) ℂ,
              ((∑ c : Fin 2, ∑ i : Fin 4,
                (p c).degreeOf i * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
                  (b c j + 1) : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, p c ≠ 0) ∧
              (∀ (c : Fin 2) (i : Fin 4), (p c).degreeOf i ≤ b c i) ∧
              (∀ c : Fin 2, ∀ x : {z : X // a z = c},
                p c ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1)) ∧
              ∀ (c : Fin 2) (i : Fin 4),
                ((U : ℕ) + 1) *
                  (Finset.univ.image (fun x : {z : X // a z = c} =>
                    (extensionChartCoordinates G.S c x.val.val) i)).card ≤ b c i + 1) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by sorry
