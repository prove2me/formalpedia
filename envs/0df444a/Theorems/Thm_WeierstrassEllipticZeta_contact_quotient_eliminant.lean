-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_contact_quotient_eliminant
-- name    : WeierstrassEllipticZeta.contact_quotient_eliminant
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T00:06:13.733122+00:00
-- url     : https://prove2.me/theorems/009c9ac3-5936-4779-b723-1f118a9f23d9
-- title:
--   A time polynomial from two finite contact quotients
-- statement:
--   Fix the elliptic-extension geometry, with its two affine charts and their derivations. Write $R=\mathbb C[t,y_1,y_2,y_3]$, let $X\subset\mathbb C$ be finite, and let $N\ge0$ be an integer. For each chart $c\in\{0,1\}$, let $J_c\subset R$ be an ideal such that $A_c=R/J_c$ is finite-dimensional over $\mathbb C$.
--
--   Assume that each $x\in X$ belongs to a valid chart $c$ in which
--   $$ J_c\subseteq I_c(x,N), $$
--   where $I_c(x,N)$ is the contact ideal of polynomials whose chart derivatives of indices below $N$ vanish at the chart point corresponding to $x$.
--
--   There is a monic polynomial $P\in\mathbb C[T]$ satisfying
--   $$ \deg P=\dim_{\mathbb C}A_0+\dim_{\mathbb C}A_1, \qquad P^{(k)}(x)=0\quad(x\in X,\ 0\le k<N). $$
--   Thus bounds on the dimensions of finite contact quotients give an explicit degree bound for a polynomial with the required vanishing derivatives. Zero-dimensional vector spaces, the empty set $X$, and $N=0$ are included.
-- source:
--   Derived contact-quotient construction for the frontier https://prove2.me/theorems/ceef0203-991e-49ad-b10f-302b3abe74db. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This supporting construction is proved using the characteristic polynomial of multiplication by the time coordinate, Cayley-Hamilton, and Taylor coefficients in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The geometric bound on the quotient dimensions is a separate open obligation.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FinCases

noncomputable section
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.contact_quotient_eliminant
    (G : Frontier.Geometry) (X : Finset ℂ) (N : ℕ)
    (J : Fin 2 → Ideal (MvPolynomial (Fin 4) ℂ))
    (hfinite : ∀ c, FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c))
    (hcontact : ∀ x ∈ X, ∃ c : Fin 2,
      G.S (extensionChartDenominator c) x ≠ 0 ∧
      J c ≤ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c x) N) :
    ∃ P : Polynomial ℂ, P.Monic ∧
      P.natDegree = ∑ c : Fin 2, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c) ∧
      ∀ x ∈ X, ∀ k < N, (Polynomial.derivative^[k] P).eval x = 0 := by sorry
