-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_claim_1
-- name    : PrivacyParadox.Alloc.claim_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:37.775887+00:00
-- url     : https://prove2.me/theorems/b62aa94e-8422-4a6f-b901-4e5c417e9cad
-- title:
--   Claim 1, p. 25 — Q(m, 1) is increasing, R(m, 1) decreasing and Q(m, 1)/R(m, 1) increasing in m
-- statement:
--   In the discrete program (39) with sorted virtual costs $0<\phi_1<\dots<\phi_K$, let $Q$ and $R$ be as in (52)–(53). For every $m$ with $1\le m<K$,
--   $$Q(m,1)<Q(m+1,1),\qquad R(m+1,1)<R(m,1),\qquad \frac{Q(m,1)}{R(m,1)}<\frac{Q(m+1,1)}{R(m+1,1)} .$$
--
--   The monotone ratio $Q(m,1)/R(m,1)$ is what the case split of the proof of Theorem 2 compares with $(B/s-l)/(\gamma\bar\theta^*)$.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 25, Claim 1

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem claim_1 (P : Prog) (hP : P.Standing) (m : ℕ) (hm1 : 1 ≤ m) (hmK : m < P.K) :
    P.Q m 1 < P.Q (m + 1) 1 ∧ P.R (m + 1) 1 < P.R m 1 ∧
      P.Q m 1 / P.R m 1 < P.Q (m + 1) 1 / P.R (m + 1) 1 := by sorry

end PrivacyParadox.Alloc
