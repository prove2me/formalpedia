-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_wp_annihilator
-- name    : WeierstrassEllipticZeta.bounded_subset_wp_annihilator
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T01:50:55.318635+00:00
-- url     : https://prove2.me/theorems/3386877f-5ae4-4d39-a745-e949468c0cff
-- title:
--   Bounded polynomials annihilating the elliptic coordinate values
-- statement:
--   Fix the elliptic-extension geometry of the current frontier. There exists a constant $C>0$ with the following property, uniform in all subsequent choices.
--
--   Retain the ambient hypotheses of [bounded_subset_period_contact_obstruction](https://prove2.me/theorems/1cf89501-706f-4434-bf47-ac8f0a87de52): positive integers $m,n,U$ with $U\le\lfloor(B(m+2n)-2)/3\rfloor$; a finite set $X\subset\mathbb C$ containing zero; a bihomogeneous polynomial $Q$ of bidegree $(m,n)$; the specified finite nonzero local orders of the normalized chart evaluations, at least $3U+1$ on $X+X+X$; the bounds $m+2n+k$ for the degrees of the $k$th chart derivatives; and both chart certificates on $X$.
--
--   For every subset $Y\subseteq X$ containing zero with
--
--   $$|Y|=\left\lfloor\frac{Cm n^2}{U+1}\right\rfloor+1,$$
--
--   there exists a nonzero polynomial $p\in\mathbb C[T]$ such that
--
--   $$2\deg p+(U+1)\le Cn^2$$
--
--   and
--
--   $$(T-\wp(z))^{U+1}\mid p(T)\qquad\text{for every }z\in Y\setminus\Lambda.$$
--
--   The polynomial may depend on all the displayed finite data. No coefficient or height bound is requested. Multiplicities are in the polynomial variable $T$; they are not asserted to follow automatically from the original chart derivative conditions. The geometric and chart-certificate assumptions stay on the ambient set $X$.
--
--   This is a sufficient algebraic construction for the current period-count frontier. The bound on its degree, including the cost of the lattice class, is the remaining open geometric estimate. It is a derived proof target, not a numbered statement quoted from the source paper.
-- source:
--   Derived reduction for https://prove2.me/theorems/1cf89501-706f-4434-bf47-ac8f0a87de52. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and the lattice-class counts used for Proposition A.1, https://doi.org/10.1017/S001309152610145X. The counting lemma is an independent deduction from the standard sigma addition identity and polynomial root multiplicities, not a quotation of the paper zero estimate. Primary Lean sources: Mathlib Algebra/Polynomial/Roots.lean, RingTheory/Coprime/Lemmas.lean, Algebra/Order/BigOperators/Group/Finset.lean and LinearAlgebra/Quotient/Defs.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The new remaining problem asks for the quantitative annihilator construction explicitly; the geometric estimate remains open.

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.bounded_subset_wp_annihilator (G : Frontier.Geometry) :
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
                ∀ z ∈ Y, z ∉ G.L.lattice →
                  (Polynomial.X - Polynomial.C (G.L.weierstrassP z)) ^ ((U : ℕ) + 1) ∣ p
                := by sorry
