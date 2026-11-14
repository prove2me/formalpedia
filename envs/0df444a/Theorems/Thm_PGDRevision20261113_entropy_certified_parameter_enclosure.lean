-- Prove2me | Theorems.Thm_PGDRevision20261113_entropy_certified_parameter_enclosure
-- name    : PGDRevision20261113.entropy_certified_parameter_enclosure
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:08:10.332733+00:00
-- url     : https://prove2.me/theorems/7736c030-7b5d-49a0-98b3-c1c174359a86
-- title:
--   A rational enclosure for the entropy-profile optimal parameters
-- statement:
--   For $\psi(t)=H(3t/4)$ and penalty $H(t)/2$ on $(-1,1)$, use the normalized power-curvature family. Take exact rational inputs
--   $$
--   (\widehat c,\widehat p)=(.4021153597,.5985245692),\qquad
--   (t_1,t_2,t_3)=(0,.7774713329,.9868532458).
--   $$
--   The signed contacts have pattern $+,-,+$ and exceed $L=.03279359$, while the error on the entire interval has norm at most $U=.03279360$.
--
--   The unique global optimal pair and rate satisfy
--   $$
--   c_*\in[.4021152,.4021156],\quad p_*\in[.5985240,.5985252],\quad
--   \rho_*\in[.03279359,.03279360].
--   $$
--   Every feasible pair in the full family $c\ge0,p>0$ with norm at most $U$ obeys the same parameter box and the same lower rate bound. All decimal inputs and endpoints are exact rationals in the formal statement.
--
--   **Related results.** [Parameter localization (Theorem 7.1)](https://prove2.me/theorems/b35f0a31-5173-472e-a00e-338bd545e1ef) · [Certified localization constants](https://prove2.me/theorems/724e9a21-4672-4c25-9520-1aa705293868) · [Rational scale endpoints](https://prove2.me/theorems/c8566766-97a3-4d51-8b5d-87b15cd4706b) · [entropy global envelope certificate](https://prove2.me/theorems/f1235fb2-7fb0-493d-822a-c04e5db4f6c1)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 7, numerical example and equation entropy_enclosures; sections/07_quantitative_certificates.tex, eq:entropy_enclosures.

import Definitions.Def_PGDRevision20261113_NumericalCertificates
open PGDRevision20261113

theorem PGDRevision20261113.entropy_certified_parameter_enclosure : EntropyNumericalEnclosureClaim := by sorry
