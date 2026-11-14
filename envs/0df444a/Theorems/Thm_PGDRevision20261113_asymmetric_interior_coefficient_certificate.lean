-- Prove2me | Theorems.Thm_PGDRevision20261113_asymmetric_interior_coefficient_certificate
-- name    : PGDRevision20261113.asymmetric_interior_coefficient_certificate
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:08:30.515325+00:00
-- url     : https://prove2.me/theorems/ba90c632-0e54-482c-b43c-5bc862aa020d
-- title:
--   Finite rational coefficient certificates for the asymmetric interior envelope
-- statement:
--   For $u\ge1$, set
--   $$
--   s=\frac{u^2-1}{u^2+1},\quad m=9+7s^2,\quad r=5/66,\quad
--   B=\frac{5184(u^2+1)^2}{625u^2},\quad
--   V=\frac{36864(u^2+1)(u+1)^2}{3125u^2},
--   $$
--   and $U=m+rB-8s$, $L=m-rB+8s$, $D=1890625u^4(u^2+1)^4$. Let $Q_+,Q_-$ be the degree-14 polynomials whose exact coefficient vectors are retained in the accompanying definition and source certificate.
--
--   The 15 monomial coefficients of $Q_+$ have minimum $11664$. If $q_i=[z^i]Q_-(1+5z)$, define
--   $$b_j=\sum_{i=0}^j\frac{\binom ji}{\binom{14}i}q_i.$$
--   The 15 rational values $b_j$ have minimum $126930799$, and the exact Bernstein expansion is
--   $$Q_-(1+5z)=\sum_{j=0}^{14}b_j\binom{14}jz^j(1-z)^{14-j}.$$
--   For $N(u)=1375u^2(u^2+1)^2L(u)$, the nine coefficients of $N(6+z)$ have maximum $-864$. The formal statement includes the exact coefficient vectors, transformation formulas, expansion, and the tail identity for $z\ge0$, where the original rational expression is defined.
--
--   **Related results.** [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [asymmetric interior algebraic factorization](https://prove2.me/theorems/0b0aafd3-0bd5-43e8-9838-a2bcc22354a2) · [exact asymmetric interior geometry example](https://prove2.me/theorems/dd5937d9-b00d-476e-9484-a2c735ba735d)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Appendix B, positive coefficients and the tail certificate; appendices/asymmetric_certificate.tex, eq:asym_positive_coefficients.

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
open PGDRevision20261113

theorem PGDRevision20261113.asymmetric_interior_coefficient_certificate : AsymmetricCoefficientCertificateClaim := by sorry
