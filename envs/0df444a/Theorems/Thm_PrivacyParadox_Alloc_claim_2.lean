-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_claim_2
-- name    : PrivacyParadox.Alloc.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:26.761511+00:00
-- url     : https://prove2.me/theorems/e73f430e-381b-4fbc-9376-8f31a1154673
-- title:
--   Claim 2, p. 26 — Q(m + 1, 1) = Q(m, φ_m/φ_{m+1}) and R(m + 1, 1) = R(m, φ_m/φ_{m+1})
-- statement:
--   In the discrete program (39) with $Q$ and $R$ as in (52)–(53), for $m=1,\dots,K-1$,
--   $$Q(m+1,1)=Q\Big(m,\frac{\phi_m}{\phi_{m+1}}\Big),\qquad R(m+1,1)=R\Big(m,\frac{\phi_m}{\phi_{m+1}}\Big).\tag{54}$$
--
--   The identities glue the curves $z\mapsto Q(m,z)$, $z\mapsto R(m,z)$ for consecutive $m$ into continuous paths, which is what the intermediate-value arguments of Claims 3 and 4 use.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 26, Claim 2, (54)

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem claim_2 (P : Prog) (hP : P.Standing) (m : ℕ) (hm1 : 1 ≤ m) (hmK : m < P.K) :
    P.Q (m + 1) 1 = P.Q m (P.phi m / P.phi (m + 1)) ∧
      P.R (m + 1) 1 = P.R m (P.phi m / P.phi (m + 1)) := by sorry

end PrivacyParadox.Alloc
