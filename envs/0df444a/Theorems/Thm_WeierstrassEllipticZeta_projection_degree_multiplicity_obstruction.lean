-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_projection_degree_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.projection_degree_multiplicity_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-12T22:57:36.369454+00:00
-- url     : https://prove2.me/theorems/80ebe548-4f16-47a2-b854-911464530876
-- title:
--   Point-count or period-class degree bound from local multiplicities
-- statement:
--   Fix the elliptic-extension geometry with its entire projective lift, compatible differential flow, truncation function $B$, and contact-ideal identities. There is a real constant $C>0$ with the following property.
--
--   Let $m,n,U\ge1$, let $X$ be a finite subset of the complex numbers containing zero, and let $Q$ be bihomogeneous of bidegree $(m,n)$. Assume the normalized derivatives have degree at most $m+2n+k$ and both charts have the fixed finite contact certificates of weight $3U+1$.
--
--   At every valid chart point, assume the normalized chart function has a unique first nonzero derivative index less than $B(m+2n)$, and locally factors as the corresponding power times an analytic function nonzero at the point. On $X+X+X$, that index is at least $3U+1$.
--
--   Then at least one of the following bounds holds, with $\Lambda$ the period lattice:
--   $$ (U+1)|X|\le Cmn^2
--   \quad\text{or}\quad
--   (U+1)|X\bmod\Lambda|\le Cn^2.$$
--   This is the remaining quantitative multiplicity estimate. The hypotheses are exactly those of the parent frontier; the conclusion is the proved equivalent numerical form of its subgroup bound.
-- source:
--   Derived projection-count equivalence for the existing frontier https://prove2.me/theorems/b8a099fb-b5c0-4096-b2bc-437cc1193a7b. The setting is Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This equivalence concerns the precise subgroup-profile conclusion already formalized in the mission; it is not a replacement for the algebraic-group multiplicity theorem in the article. It uses quotient maps, finite image cardinalities, and monotonicity of powers at Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.projection_degree_multiplicity_obstruction (G : Frontier.Geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
          1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
          0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
            (∀ d ∈ Q.support, d 0 + d 1 = m ∧
              d 2 + d 3 + d 4 + d 5 + d 6 = n) →
            (∀ (c : Fin 2) (z : ℂ), G.S (extensionChartDenominator c) z ≠ 0 →
              let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
                (extensionChartNormalize c Q)
              ∃! k : ℕ, k < G.B (m + 2 * n) ∧
                (z ∈ X + X + X → 3 * U + 1 ≤ k) ∧
                (∀ j < k, iteratedDeriv j f z = 0) ∧ iteratedDeriv k f z ≠ 0 ∧
                ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
                  f =ᶠ[𝓝 z] (fun w => (w - z) ^ k * g w)) →
            (∀ (c : Fin 2) (k : ℕ),
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
                m + 2 * n + k) →
            Frontier.HasChartCertificates G m n U X Q →
            (((U + 1 : ℕ) : ℝ) * X.card ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∨
              ((U + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by sorry
