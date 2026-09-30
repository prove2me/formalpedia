-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_border_reduction_contact_obstruction
-- name    : WeierstrassEllipticZeta.border_reduction_contact_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-13T02:18:08.490727+00:00
-- url     : https://prove2.me/theorems/bd5bb8a3-3114-4e8d-883c-ee2a0555c3c9
-- title:
--   Small monomial boundaries at contacts or a period-class bound
-- statement:
--   Fix the elliptic-extension geometry, its entire projective lift, differential flow, truncation function $B$, and contact-ideal identities. There exists a constant $C>0$ that works uniformly as follows.
--
--   For every $m,n\ge1$, consider
--   $$1\le U\le\left\lfloor\frac{B(m+2n)-2}{3}\right\rfloor.$$
--   Let $X\subset\mathbb C$ be finite and contain zero, and let $Q$ be bihomogeneous of bidegree $(m,n)$. Assume the normalized chart derivatives have degree at most $m+2n+k$ and the fixed chart certificates have weight $3U+1$.
--
--   At every valid chart point, assume the normalized function has a unique first nonzero derivative index below $B(m+2n)$, together with the corresponding analytic local power factorization. On $X+X+X$, this index is at least $3U+1$.
--
--   Then either there are finite exponent sets $S_0,S_1\subset\mathbb N^4$ containing zero and, for each $a$ in the boundary
--   $$\partial S_c=\{d+e_i:d\in S_c,\ i=0,1,2,3\}\setminus S_c,$$
--   a polynomial $b_{c,a}\in\mathbb C[t,y_1,y_2,y_3]$ supported in $S_c$, such that
--   $$|S_0|+|S_1|\le Cmn^2$$
--   and every $x\in X$ has a valid chart $c$ with
--   $$X^a-b_{c,a}\in I_c(x,U+1)\qquad(a\in\partial S_c),$$
--   or the period lattice $\Lambda$ satisfies
--   $$ (U+1)|X\bmod\Lambda|\le Cn^2.$$
--
--   Here $I_c(x,U+1)$ is the ideal of polynomials whose chart derivatives of orders zero through $U$ vanish at $x$. The constant is independent of the degree pair, the weight, the finite set, and the polynomial.
-- source:
--   Derived monomial-boundary completion for the frontier https://prove2.me/theorems/27b4055a-78d2-4844-86a1-29fa1008c8d7. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting result completes boundary relations to all coordinate products and proves equivalence of ideal containment in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The uniform geometric construction remains open.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.border_reduction_contact_obstruction (G : Frontier.Geometry) :
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
            ((∃ S : Fin 2 → Finset (Fin 4 →₀ ℕ),
              let B := fun c : Fin 2 => (Finset.univ.biUnion fun i : Fin 4 =>
                (S c).image (fun d => d + Finsupp.single i 1)) \ S c
              ∃ b : Fin 2 → (Fin 4 →₀ ℕ) → MvPolynomial (Fin 4) ℂ,
              ((∑ c : Fin 2, (S c).card : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, 0 ∈ S c) ∧
              (∀ c : Fin 2, ∀ e ∈ B c, (b c e).support ⊆ S c) ∧
              ∀ x ∈ X, ∃ c : Fin 2,
                G.S (extensionChartDenominator c) x ≠ 0 ∧
                ∀ e ∈ B c, MvPolynomial.monomial e 1 - b c e ∈
                  extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                    (extensionChartCoordinates G.S c x) ((U : ℕ) + 1)) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by sorry
