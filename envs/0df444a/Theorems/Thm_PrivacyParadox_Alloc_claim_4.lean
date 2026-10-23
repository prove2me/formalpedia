-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_claim_4
-- name    : PrivacyParadox.Alloc.claim_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:34.970888+00:00
-- url     : https://prove2.me/theorems/28d71f32-1c41-4f6e-b2d0-f72de6d6a2f9
-- title:
--   Claim 4, p. 30 — in Case 2(b) there are k′ ∈ {1, …, m*} and z′ ∈ (φ_{k′}/φ_{k′+1}, 1] with R(k′, z′) = γθ̄*
-- statement:
--   In the discrete program (39), let $m^*\in\{1,\dots,K-1\}$ and $z^*\in(\phi_{m^*}/\phi_{m^*+1},1]$ satisfy (58), $Q(m^*,z^*)/R(m^*,z^*)=(B/s-l)/(\gamma\bar\theta^*)$, and assume the Case 2(b) condition
--   $$\frac{B/s-l}{Q(m^*,z^*)}>1 .$$
--   Then there exist $k'\in\{1,\dots,m^*\}$ and $z'\in(\phi_{k'}/\phi_{k'+1},1]$ such that
--   $$R(k',z')=\gamma\bar\theta^*.\tag{61}$$
--
--   The pair $(k',z')$ determines the adversary's best response in Case 2(b), where the allocation saturates at $1$ on the cheapest cells.
--
--   **Formalization Note** The hypotheses are the conclusion of Claim 3 and the Case 2(b) condition of p. 30.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 30, Claim 4, (61) (Case 2(b) condition on the same page)

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem claim_4 (P : Prog) (hP : P.Standing) (m : ℕ) (hm : m ∈ Finset.Icc 1 (P.K - 1))
    (z : ℝ) (hz : P.phi m / P.phi (m + 1) < z ∧ z ≤ 1)
    (h58 : P.Q m z / P.R m z = (P.B / P.s - P.l) / (P.gam * P.theta))
    (h2b : 1 < (P.B / P.s - P.l) / P.Q m z) :
    ∃ k' ∈ Finset.Icc 1 m, ∃ z' : ℝ, P.phi k' / P.phi (k' + 1) < z' ∧ z' ≤ 1 ∧
      P.R k' z' = P.gam * P.theta := by sorry

end PrivacyParadox.Alloc
