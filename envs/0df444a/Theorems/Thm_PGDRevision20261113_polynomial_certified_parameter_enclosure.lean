-- Prove2me | Theorems.Thm_PGDRevision20261113_polynomial_certified_parameter_enclosure
-- name    : PGDRevision20261113.polynomial_certified_parameter_enclosure
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:08:14.222761+00:00
-- url     : https://prove2.me/theorems/6c0c0b6c-4737-4568-a58f-d86e22604aae
-- title:
--   A rational enclosure for polynomial-curvature geometry design
-- statement:
--   On $(-1,1)$ let $f(t)=t^2/2+t^6/30$, $g(t)=H(t)$, and $\phi_c(t)=t^2/2+ct^4/12$ for $c\ge0$. Thus
--   $$A=1+t^4,\quad B=(1-t^2)^{-1},\quad k_c=1+ct^2.$$
--   Use exact rational candidate $(\widehat c,\widehat p)=(.70413511497404,.95214943774562)$ and contacts with squared radii $(0,.30185874876975,.84343777215832)$ and signs $-,+,-$.
--
--   The candidate has a global envelope $U=.02451174$ and signed contact lower bound $L=.02451173$. The full feasible family has a unique minimizing pair with
--   $$
--   c_*\in[.7041345,.7041354],\quad p_*\in[.9521489,.9521500],\quad
--   \rho_*\in[.02451173,.02451174].
--   $$
--   Every improving pair with norm at most $U$ obeys that box and lower rate bound. Its exponent is also at most $1896437301989138/2378943363494569<2$, so restricting the localization argument to $[0,2]$ loses no improving pair. The actual implicit updates are well-defined and $\Omega_N=\rho^{2N}$ for every feasible fixed pair and finite $N\ge1$.
--
--   **Related results.** [Parameter localization (Theorem 7.1)](https://prove2.me/theorems/b35f0a31-5173-472e-a00e-338bd545e1ef) · [Certified localization constants](https://prove2.me/theorems/724e9a21-4672-4c25-9520-1aa705293868) · [Rational scale endpoints](https://prove2.me/theorems/c8566766-97a3-4d51-8b5d-87b15cd4706b) · [polynomial global envelope certificate](https://prove2.me/theorems/6c29080d-f4b9-4000-b2b8-b6e8009d33a5)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Reproducibility supplement, polynomial geometry certificate; reproducibility/certify_geometry.py, polynomial_certificate; results/polynomial_geometry_certificate.json.

import Definitions.Def_PGDRevision20261113_NumericalCertificates
open PGDRevision20261113

theorem PGDRevision20261113.polynomial_certified_parameter_enclosure : PolynomialNumericalEnclosureClaim := by sorry
