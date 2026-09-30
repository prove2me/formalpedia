-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_wp_contact_polynomial
-- name    : WeierstrassEllipticZeta.bounded_subset_wp_contact_polynomial
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T02:26:10.422005+00:00
-- url     : https://prove2.me/theorems/c9f70c21-a452-4c12-aa1e-5a4861562a6d
-- title:
--   Bounded polynomials with high analytic contact in the elliptic coordinate
-- statement:
--   Fix the elliptic-extension geometry of the current frontier. There is a constant $C>0$, uniform in the following data.
--
--   Keep all the hypotheses of [bounded_subset_wp_annihilator](https://prove2.me/theorems/3386877f-5ae4-4d39-a745-e949468c0cff): positive integers $m,n,U$ with $U\le\lfloor(B(m+2n)-2)/3\rfloor$; a finite set $X\subset\mathbb C$ containing zero; a bihomogeneous polynomial $Q$ of bidegree $(m,n)$; the prescribed finite nonzero orders of the normalized chart evaluations, at least $3U+1$ on $X+X+X$; degree bounds $m+2n+k$ on the iterated chart derivatives; and both chart certificates on $X$.
--
--   For each $Y\subseteq X$ containing zero with
--
--   $$|Y|=\left\lfloor\frac{Cm n^2}{U+1}\right\rfloor+1,$$
--
--   there is a nonzero polynomial $p\in\mathbb C[T]$ such that
--
--   $$2\deg p+(U+1)\le Cn^2$$
--
--   and
--
--   $$\left.\frac{d^j}{dw^j}p(\wp(w))\right|_{w=z}=0
--   \qquad(z\in Y\setminus\Lambda,\ 0\le j<3U+1).$$
--
--   The constant depends only on the fixed geometry; the polynomial may depend on all the finite data. There is no coefficient or height requirement. No contact condition is imposed at lattice points, where $\wp$ has a pole.
--
--   This is a derived target for the quantitative polynomial construction. Its contact condition concerns the new polynomial $p$, so it still must be deduced from the hypotheses on $Q$. The analytic multiplicity transfer is proved separately. The uniform degree and contact construction remains open; this statement does not assert the full zero estimate from the paper.
-- source:
--   Derived analytic-to-algebraic reduction for https://prove2.me/theorems/3386877f-5ae4-4d39-a745-e949468c0cff. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. The new lemma is an independent deduction from the normalized entire sigma differential data, sigma addition, and zeta quasi-periodicity, not a quotation of the paper zero estimate. It proves the local multiplicity bound two for wp and transfers analytic contact to polynomial root divisibility. Primary Lean sources: Mathlib Analysis/Analytic/Order.lean (analyticOrderAt_comp, analyticOrderAt_mul), Algebra/Polynomial/Div.lean (root-multiplicity factorization), and Analysis/Normed/Module/Connected.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The remaining statement explicitly retains the quantitative construction of a polynomial with high contact; no geometric degree estimate is being claimed as proved.

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.bounded_subset_wp_contact_polynomial (G : Frontier.Geometry) :
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
              ∃ p : Polynomial ℂ, p ≠ 0 ∧
                ((2 * p.natDegree + ((U : ℕ) + 1) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
                ∀ z ∈ Y, z ∉ G.L.lattice → ∀ j < 3 * (U : ℕ) + 1,
                  iteratedDeriv j (fun w => p.eval (G.L.weierstrassP w)) z = 0
                := by sorry
