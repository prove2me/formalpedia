-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_frontier_local_multiplicity
-- name    : WeierstrassEllipticZeta.frontier_local_multiplicity
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-12T22:37:51.53853+00:00
-- url     : https://prove2.me/theorems/5eff65dc-adfb-48ee-8bed-fb1e269f27be
-- title:
--   Exact local multiplicity of the normalized chart function
-- statement:
--   Fix the elliptic-extension geometry, the two finite chart certificates for a polynomial $Q$, and a valid chart point $z$. Write
--   $$f(w)=Q_c(\operatorname{coords}_c(w)),\qquad D=B(m+2n).$$
--   If the analytic order of $f$ at $z$ is less than $D$, then there is a unique natural number $k<D$ such that every derivative of index less than $k$ vanishes at $z$, the derivative of index $k$ is nonzero, and
--   $$f(w)=(w-z)^k g(w)$$
--   on a neighborhood of $z$, for some function $g$ analytic at $z$ with nonzero value there. At points of $X+X+X$, this same integer also satisfies
--   $$3U+1\le k.$$
--   The theorem includes zero multiplicity away from the prescribed contact set. Only the multiplicity is claimed unique; the witness function is specified locally.
-- source:
--   Derived local analytic step for Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The local order/factorization lemma is derived here using Mathlib Analysis.Analytic.Order at commit 0df444a360eaa60ab8c11dca51a86af692955474; it is not a quoted statement of the article. The selected parent is https://prove2.me/theorems/0e52411c-8d52-4214-8b0a-33cdfdfb9c63.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.frontier_local_multiplicity
    (G : Frontier.Geometry) (m n U : ℕ) (X : Finset ℂ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (hcharts : Frontier.HasChartCertificates G m n U X Q)
    (c : Fin 2) (z : ℂ)
    (hz : G.S (extensionChartDenominator c) z ≠ 0)
    (hupper : analyticOrderAt
      (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
        (extensionChartNormalize c Q)) z < G.B (m + 2 * n)) :
    let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
      (extensionChartNormalize c Q)
    ∃! k : ℕ, k < G.B (m + 2 * n) ∧
      (z ∈ X + X + X → 3 * U + 1 ≤ k) ∧
      (∀ j < k, iteratedDeriv j f z = 0) ∧ iteratedDeriv k f z ≠ 0 ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
        f =ᶠ[𝓝 z] (fun w => (w - z) ^ k * g w) := by sorry
