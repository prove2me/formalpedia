-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_canonical_box_contact_obstruction
-- name    : WeierstrassEllipticZeta.canonical_box_contact_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-13T21:13:41.146651+00:00
-- url     : https://prove2.me/theorems/b9f04d31-9d16-4432-b4ad-69b15ccf7af4
-- title:
--   Contact obstruction with explicit canonical box weights
-- statement:
--   Under the same geometry, local-order, derivative-degree, and chart-certificate hypotheses as `coordinate_value_count_contact_obstruction`, find a positive uniform constant C giving its period-class alternative or valid chart assignments a and nonzero contact polynomials p_c with the following explicit bound.
--
--   Write d_ci=degree_i(p_c), let T_ci be the finite set of distinct i-th coordinate values of points assigned to chart c, and set t_ci=(U+1)|T_ci|. Require
--
--   $$\sum_{c=0}^1\sum_{i=0}^3 d_{ci}\prod_{j\ne i}\max(d_{cj}+1,t_{cj})
--   \le Cmn^2.$$
--
--   Each p_c must still belong to every order-(U+1) contact ideal at the points assigned to c. This statement eliminates the existential box bounds and replaces their admissibility constraints with the exact minimum weighted-face expression. It is equivalent to the selected frontier; it adds no geometric hypothesis. Establishing this explicit estimate or the period-class alternative remains open.
-- source:
--   Derived exact box minimization for the frontier https://prove2.me/theorems/7474c39b-a6ed-4850-82c1-ddace253bc6b. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The combinatorial certificate is derived using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Data/Finsupp/Defs.lean (equivFunOnFinite) and Algebra/Order/BigOperators/Group/Finset.lean (prod_le_prod', sum_le_sum), with elementary natural-number order and truncated subtraction. The new geometric child is equivalent to the selected frontier: the canonical side length is max(degree+1, contact order times coordinate-value count). The uniform geometric estimate and the main mission theorem remain open.

import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.canonical_box_contact_obstruction (G : Frontier.Geometry) :
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
              ∃ p : Fin 2 → MvPolynomial (Fin 4) ℂ,
              ((∑ c : Fin 2, ∑ i : Fin 4,
                (p c).degreeOf i * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
                  max ((p c).degreeOf j + 1)
                    (((U : ℕ) + 1) *
                      (Finset.univ.image (fun x : {z : X // a z = c} =>
                        (extensionChartCoordinates G.S c x.val.val) j)).card) : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, p c ≠ 0) ∧
              (∀ c : Fin 2, ∀ x : {z : X // a z = c},
                p c ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1))) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by sorry
