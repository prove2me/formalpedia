-- Prove2me | Theorems.Thm_PGDRevision20261113_entropy_global_envelope_certificate
-- name    : PGDRevision20261113.entropy_global_envelope_certificate
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:08:22.377047+00:00
-- url     : https://prove2.me/theorems/f1235fb2-7fb0-493d-822a-c04e5db4f6c1
-- title:
--   The entropy example has a global envelope, endpoint tail, and score-gap bounds
-- statement:
--   For the entropy example $A=(9/16)/(1-(9/16)t^2)$, $B=1/[2(1-t^2)]$, use $c=.4021153597$, $p=.5985245692$, and radii $(0,.7774713329,.9868532458)$.
--
--   The following continuum and point bounds hold:
--   $$
--   |E(t)|\le .03279360\ (0\le t\le .9999),\qquad
--   |E(t)|<.005465\ (.9999\le t<1),
--   $$
--   and all three signed contacts $+,-,+$ are strictly larger than $.03279359$.
--
--   For $J_c(t)=\partial_c\log k_c(t)$ and every $c\in[0,2]$, both adjacent score gaps satisfy
--   $$J_c(t_j)-J_c(t_i)\ge\frac{t_j^2-t_i^2}{2-t_i^2-t_j^2}\quad((i,j)=(1,2),(2,3)),$$
--   and $|J_c(t_i)|\le5$. These assertions supply the global and localization ingredients of the rational parameter enclosure. The source's Arb cover and tail estimate are retained as reproducibility data.
--
--   **Related results.** [Parameter localization (Theorem 7.1)](https://prove2.me/theorems/b35f0a31-5173-472e-a00e-338bd545e1ef) · [entropy certified parameter enclosure](https://prove2.me/theorems/7736c030-7b5d-49a0-98b3-c1c174359a86)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 7, final numerical example and reproduction certificate; sections/07_quantitative_certificates.tex, eq:entropy_enclosures; reproducibility/certify_geometry.py entropy_certificate.

import Definitions.Def_PGDRevision20261113_NumericalCertificates
open PGDRevision20261113

theorem PGDRevision20261113.entropy_global_envelope_certificate : EntropyGlobalEnvelopeClaim := by sorry
