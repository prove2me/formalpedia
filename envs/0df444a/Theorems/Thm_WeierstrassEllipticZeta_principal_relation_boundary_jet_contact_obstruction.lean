-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_principal_relation_boundary_jet_contact_obstruction
-- name    : WeierstrassEllipticZeta.principal_relation_boundary_jet_contact_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-13T03:38:03.7414+00:00
-- url     : https://prove2.me/theorems/a0d7189b-1242-47eb-bf90-6587bb9a2e25
-- title:
--   Enough supported monomial multiples at contacts or a period-class bound
-- statement:
--   Fix the elliptic-extension geometry, its entire projective lift, differential flow, truncation function $B$, and contact-ideal identities. There exists a constant $C>0$ that works uniformly as follows.
--
--   For every $m,n\ge1$, consider
--   $$1\le U\le\left\lfloor\frac{B(m+2n)-2}{3}\right\rfloor.$$
--   Let $X\subset\mathbb C$ be finite and contain zero, and let $Q$ be bihomogeneous of bidegree $(m,n)$. Assume the normalized chart derivatives have degree at most $m+2n+k$ and the fixed chart certificates have weight $3U+1$.
--
--   At every valid chart point, assume the normalized function has a unique first nonzero derivative index below $B(m+2n)$, together with its analytic local power factorization. On $X+X+X$, this index is at least $3U+1$.
--
--   Then either one can assign each $x\in X$ to a valid chart $a(x)\in\{0,1\}$ and choose finite exponent sets $S_0,S_1,T_0,T_1\subset\mathbb N^4$ and nonzero chart polynomials $p_0,p_1$ with the following properties. Each $S_c$ contains zero, and
--   $$|S_0|+|S_1|\le Cmn^2+|T_0|+|T_1|.$$
--   For $d\in T_c$, the polynomial $p_cX^d$ is supported in $S_c$. At every point assigned to chart $c$, the polynomial $p_c$ belongs to the contact ideal of order $U+1$.
--
--   Let $\mathcal J_c(q)$ be the vector of chart derivatives of $q$ of orders $0$ through $U$, evaluated at every point assigned to chart $c$, and put
--   $$V_c=\operatorname{span}_{\mathbb C}\{\mathcal J_c(X^d):d\in S_c\},\qquad
--   \partial S_c=\{d+e_i:d\in S_c,\ i=0,1,2,3\}\setminus S_c.$$
--   For each chart, adjoining the boundary jet vectors preserves the dimension:
--   $$\dim_{\mathbb C}\operatorname{span}\{\mathcal J_c(X^d):d\in S_c\cup\partial S_c\}
--   =\dim_{\mathbb C}V_c.$$
--
--   Or the period lattice $\Lambda$ satisfies
--   $$ (U+1)|X\bmod\Lambda|\le Cn^2.$$
--
--   Each chart uses a single polynomial $p_c$ at all its assigned contacts. The constant is independent of the degree pair, the weight, the finite set, and the polynomial $Q$.
-- source:
--   Derived construction of supported relation spaces for the frontier https://prove2.me/theorems/2053281f-559d-4942-9256-658282218fcc. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting construction uses injectivity of multiplication by a nonzero polynomial, finite monomial bases, and closure of ideals under multiplication in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The uniform geometric support and cardinality construction remains open.

import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.principal_relation_boundary_jet_contact_obstruction (G : Frontier.Geometry) :
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
              ∃ S : Fin 2 → Finset (Fin 4 →₀ ℕ),
              let B := fun c : Fin 2 => (Finset.univ.biUnion fun i : Fin 4 =>
                (S c).image (fun d => d + Finsupp.single i 1)) \ S c
              let jets := fun (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ)
                (x : {z : X // a z = c}) (k : Fin ((U : ℕ) + 1)) =>
                  MvPolynomial.eval (extensionChartCoordinates G.S c x.val.val)
                    ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val] p)
              ∃ p : Fin 2 → MvPolynomial (Fin 4) ℂ,
              ∃ T : Fin 2 → Finset (Fin 4 →₀ ℕ),
              ((∑ c : Fin 2, (S c).card : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 +
                ((∑ c : Fin 2, (T c).card : ℕ) : ℝ) ∧
              (∀ c : Fin 2, p c ≠ 0) ∧
              (∀ c : Fin 2, ∀ d ∈ T c,
                (p c * MvPolynomial.monomial d 1).support ⊆ S c) ∧
              (∀ c : Fin 2, ∀ x : {z : X // a z = c},
                p c ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1)) ∧
              (∀ c : Fin 2, 0 ∈ S c) ∧
              ∀ c : Fin 2,
                Module.finrank ℂ (Submodule.span ℂ
                  ((fun d : Fin 4 →₀ ℕ => jets c (MvPolynomial.monomial d 1)) ''
                    ((S c ∪ B c : Finset (Fin 4 →₀ ℕ)) : Set (Fin 4 →₀ ℕ)))) =
                Module.finrank ℂ (Submodule.span ℂ
                  ((fun d : Fin 4 →₀ ℕ => jets c (MvPolynomial.monomial d 1)) ''
                    (S c : Set (Fin 4 →₀ ℕ))))) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by sorry
