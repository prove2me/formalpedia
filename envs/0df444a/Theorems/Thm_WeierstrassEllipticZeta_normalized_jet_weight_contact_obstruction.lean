-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_normalized_jet_weight_contact_obstruction
-- name    : WeierstrassEllipticZeta.normalized_jet_weight_contact_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-13T21:59:02.027823+00:00
-- url     : https://prove2.me/theorems/f549933d-0d83-4a02-b869-0ccbdb73c16a
-- title:
--   A sufficient weighted bound for a finite normalized-jet family
-- statement:
--   Under the same hypotheses as `canonical_box_contact_obstruction`, prove its period-class alternative or find a valid chart assignment a and one integer k_c in {0,…,2U} for each chart such that the following explicit polynomials meet the canonical weighted-face estimate:
--
--   $$p_c=\begin{cases}
--   D_c^{k_c}(\operatorname{Normalize}_c Q),&\text{if a point is assigned to c},\\
--   1,&\text{otherwise}.
--   \end{cases}$$
--
--   Write d_ci=degree_i(p_c) and let T_ci be the finite set of i-th coordinate values of the assigned points. The required estimate is
--
--   $$\sum_c\sum_i d_{ci}\prod_{j\ne i}\max(d_{cj}+1,(U+1)|T_{cj}|)\le Cmn^2$$
--
--   for one positive C depending only on G. The period-class alternative is unchanged. This is a sufficient criterion restricting the polynomial witnesses to a finite normalized-jet family. Equivalence to the selected frontier's unrestricted polynomial choice is not claimed. Establishing the weight estimate or the period-class alternative remains open.
-- source:
--   Derived normalized-jet contact certificate for the frontier https://prove2.me/theorems/b9f04d31-9d16-4432-b4ad-69b15ccf7af4. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The complete proof derives a finite family from the existing ChartCertificate.polynomial.triangular.orders and Geometry.hcontact hypotheses, using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Logic/Function/Iterate.lean (iterate_add_apply, iterate_succ_apply'). The remaining child is a sufficient finite-family weight criterion, not an asserted equivalent reformulation of unrestricted contact-polynomial choice. Its uniform geometric estimate and the main mission theorem remain open.

import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.normalized_jet_weight_contact_obstruction (G : Frontier.Geometry) :
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
              ∃ k : Fin 2 → Fin (2 * (U : ℕ) + 1),
              let p := fun c : Fin 2 =>
                if Nonempty {z : X // a z = c} then
                  (extensionChartDerivation G.L.g₂ G.L.g₃ c)^[(k c).val]
                    (extensionChartNormalize c Q)
                else 1
              ((∑ c : Fin 2, ∑ i : Fin 4,
                (p c).degreeOf i * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
                  max ((p c).degreeOf j + 1)
                    (((U : ℕ) + 1) *
                      (Finset.univ.image (fun x : {z : X // a z = c} =>
                        (extensionChartCoordinates G.S c x.val.val) j)).card) : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by sorry
