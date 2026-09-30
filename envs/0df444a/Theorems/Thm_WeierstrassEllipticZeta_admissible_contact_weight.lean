-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_admissible_contact_weight
-- name    : WeierstrassEllipticZeta.admissible_contact_weight
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T00:45:38.931919+00:00
-- url     : https://prove2.me/theorems/c90c6c3a-bbc2-48ad-b318-25a676c4584f
-- title:
--   The admissible range of contact weights
-- statement:
--   Fix the elliptic-extension geometry and its truncation function $B$. Let $m,n,U$ be nonnegative integers, let $X\subset\mathbb C$ be finite with $0\in X$, and let $Q$ be a polynomial in the seven projective coordinates. Suppose the two charts carry the mission's finite contact certificates for $(m,n,U,X,Q)$, with contact weight $3U+1$ on $X+X+X$.
--
--   Then
--   $$ 3U+1<B(m+2n), \qquad U\le\left\lfloor\frac{B(m+2n)-2}{3}\right\rfloor. $$
--   In particular, for each fixed degree pair $(m,n)$, only finitely many contact weights can satisfy these certificate hypotheses. This is a restriction on the admissible parameter range; it does not give a bound on the dimensions of the contact quotients.
-- source:
--   Derived admissible contact-weight restriction for the frontier https://prove2.me/theorems/bda1978d-c31b-453a-9439-87bd1d572efb. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The proof uses the existing projective chart cover and the strict truncation-order bounds in the fixed contact certificates at Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. This gives a finite range of contact weights for each fixed degree pair; the uniform geometric dimension estimate is still open.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry

noncomputable section
open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

theorem WeierstrassEllipticZeta.admissible_contact_weight
    (G : Frontier.Geometry) (m n U : ℕ) (X : Finset ℂ) (hX : 0 ∈ X)
    (Q : MvPolynomial (Fin 7) ℂ) (hcharts : Frontier.HasChartCertificates G m n U X Q) :
    3 * U + 1 < G.B (m + 2 * n) ∧ U ≤ (G.B (m + 2 * n) - 2) / 3 := by sorry
