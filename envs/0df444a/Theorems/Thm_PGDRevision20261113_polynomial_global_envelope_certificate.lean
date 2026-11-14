-- Prove2me | Theorems.Thm_PGDRevision20261113_polynomial_global_envelope_certificate
-- name    : PGDRevision20261113.polynomial_global_envelope_certificate
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:08:17.545024+00:00
-- url     : https://prove2.me/theorems/6c29080d-f4b9-4000-b2b8-b6e8009d33a5
-- title:
--   A global rational envelope and three signed contacts for the polynomial example
-- statement:
--   Set $p=.95214943774562$, $c=.70413511497404$, and
--   $$
--   e(u)=\frac{[p(1+cu)-(1+u^2)](1-u)}{p(1+cu)(1-u)+1}.
--   $$
--   The exact rational certificate asserts
--   $$|e(u)|\le .02451174\quad(0\le u\le1).$$
--   At squared radii $(0,.30185874876975,.84343777215832)$ the signed values, with signs $-,+,-$, are all strictly larger than $.02451173$. The endpoint at $u=1$ is included in this rational envelope. These are statements on a continuum, rather than constraints at a finite grid.
--
--   **Related results.** [Parameter localization (Theorem 7.1)](https://prove2.me/theorems/b35f0a31-5173-472e-a00e-338bd545e1ef) · [polynomial certified parameter enclosure](https://prove2.me/theorems/6c0c0b6c-4737-4568-a58f-d86e22604aae)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Reproducibility supplement, polynomial certificate; reproducibility/certify_geometry.py, polynomial_certificate.

import Definitions.Def_PGDRevision20261113_NumericalCertificates
open PGDRevision20261113

theorem PGDRevision20261113.polynomial_global_envelope_certificate : PolynomialGlobalEnvelopeClaim := by sorry
