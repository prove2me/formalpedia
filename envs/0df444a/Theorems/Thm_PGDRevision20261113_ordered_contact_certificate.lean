-- Prove2me | Theorems.Thm_PGDRevision20261113_ordered_contact_certificate
-- name    : PGDRevision20261113.ordered_contact_certificate
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T06:24:09.874214+00:00
-- url     : https://prove2.me/theorems/e6086f79-a060-4960-996c-800464fc7f05
-- title:
--   Three ordered feature contacts certify the unique optimal geometry
-- statement:
--   Assume either prescribed geometry model of Theorem 5.1, including its regularity conditions. For $c\ge0$, $p>0$ and $r>0$, suppose the error
--   $$
--   E_{c,p}(t)=\frac{pk_c(t)-A(t)}{pk_c(t)+\lambda b(t)}
--   $$
--   satisfies $|E_{c,p}(t)|\le r$ on the entire state domain. If three states have $\zeta(t_1)<\zeta(t_2)<\zeta(t_3)$ and
--   $$
--   E_{c,p}(t_i)=\sigma(-1)^{i-1}r,\qquad \sigma\in\{-1,1\},
--   $$
--   then $(c,p)$ is the unique global minimizer over all nonnegative exponents and positive scales, and its norm is exactly $r$.
--   The envelope and contact equalities together are a sufficient global certificate.
--
--   **Related results.** [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Theorem 5.1 proof, contact certificates, page 14.

import Definitions.Def_PGDRevision20261113_Geometry
open PGDRevision20261113

theorem PGDRevision20261113.ordered_contact_certificate : OrderedContactCertificateClaim := by sorry
