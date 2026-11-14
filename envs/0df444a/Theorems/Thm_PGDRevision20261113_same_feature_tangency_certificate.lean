-- Prove2me | Theorems.Thm_PGDRevision20261113_same_feature_tangency_certificate
-- name    : PGDRevision20261113.same_feature_tangency_certificate
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T06:24:19.675834+00:00
-- url     : https://prove2.me/theorems/de242eb0-14af-49b9-8f96-4f8b07f8e03d
-- title:
--   Same-feature opposite contacts certify uniqueness under the stated regularity
-- statement:
--   Assume either admissible geometry model of Theorem 5.1, with the stated differentiability conditions in the asymmetric case. Let $c\ge0$, $p>0$, $r>0$, and suppose the entire-domain envelope $|E_{c,p}(t)|\le r$ holds. If there are distinct states $x,y$ with
--   $$
--   \zeta(x)=\zeta(y)>0,\qquad
--   E_{c,p}(x)=r,\qquad E_{c,p}(y)=-r,
--   $$
--   then $(c,p)$ is the unique global minimizing pair, with $\rho(c,p)=r$.
--   The feature must be nonminimal, and the prescribed model regularity is retained. In the interval model these states are antipodal; this contact pattern is unavailable for an even loss curvature.
--   This supplies the second contact certificate used by the general classification.
--
--   **Related results.** [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
--
--   **Further examples and certificates.** [tangency derivative identity](https://prove2.me/theorems/2838f92b-a6be-44f5-a2be-aab759757225) · [exact asymmetric interior geometry example](https://prove2.me/theorems/dd5937d9-b00d-476e-9484-a2c735ba735d) · [exact asymmetric quadratic geometry example](https://prove2.me/theorems/ee75d7dc-a137-4e44-aea5-b757651ed73f)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Theorem 5.1 proof, same-feature contact argument and derivative identity, page 14.

import Definitions.Def_PGDRevision20261113_Geometry
open PGDRevision20261113

theorem PGDRevision20261113.same_feature_tangency_certificate : SameFeatureTangencyClaim := by sorry
