-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_time_eliminant_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.time_eliminant_multiplicity_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-12T23:35:20.655852+00:00
-- url     : https://prove2.me/theorems/ceef0203-991e-49ad-b10f-302b3abe74db
-- title:
--   Polynomial certificate or period-class multiplicity bound
-- statement:
--   Fix the elliptic-extension geometry, including its projective lift, compatible differential flow, truncation function $B$, and contact-ideal identities. There is a constant $C>0$ with the following property.
--
--   Let $m,n,U\ge1$, let $X$ be a finite subset of the complex numbers containing zero, and let $Q$ be bihomogeneous of bidegree $(m,n)$. Retain the normalized derivative degree bound, both fixed chart certificates, and the parent's local analytic factorization and first-nonzero-derivative assumptions. The local order is less than $B(m+2n)$ everywhere in a valid chart and at least $3U+1$ on $X+X+X$.
--
--   Then either there is a nonzero univariate complex polynomial $P$ satisfying
--   $$ \deg P\le Cmn^2,\qquad P^{(k)}(x)=0\quad(x\in X,\ 0\le k<U+1), $$
--   or the period-class bound holds:
--   $$ (U+1)|X\bmod\Lambda|\le Cn^2, $$
--   where $\Lambda$ is the period lattice.
--
--   The first alternative is a concrete polynomial certificate for the parent's point-count bound. All hypotheses and the period-class alternative are unchanged. Constructing a certificate of the required degree from the geometric hypotheses, or establishing the period alternative, remains the open quantitative step.
-- source:
--   Derived finite-jet degree criterion for the frontier https://prove2.me/theorems/80ebe548-4f16-47a2-b854-911464530876. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The polynomial criterion is proved here from Taylor coefficients and coprime root powers in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. It is a supporting reduction, not a claim to have proved the article's geometric multiplicity estimate.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.time_eliminant_multiplicity_obstruction (G : Frontier.Geometry) :
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
            ((∃ P : Polynomial ℂ, P ≠ 0 ∧
              (P.natDegree : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              ∀ x ∈ X, ∀ k < U + 1, (Polynomial.derivative^[k] P).eval x = 0) ∨
              ((U + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by sorry
