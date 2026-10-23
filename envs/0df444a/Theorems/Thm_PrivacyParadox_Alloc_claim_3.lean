-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_claim_3
-- name    : PrivacyParadox.Alloc.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:26.121385+00:00
-- url     : https://prove2.me/theorems/07fbf408-d6fa-4886-a1fa-3e4109a4a582
-- title:
--   Claim 3, p. 28 — in Case 2 there are m* ∈ {1, …, K − 1} and z* ∈ (φ_{m*}/φ_{m*+1}, 1] with Q(m*, z*)/R(m*, z*) = (B/s − l)/(γθ̄*)
-- statement:
--   In the discrete program (39), assume the Case 2 condition of the proof of Theorem 2,
--   $$\frac{Q(1,1)}{R(1,1)}\le\frac{B/s-l}{\gamma\bar\theta^*}<\frac{Q(K,1)}{R(K,1)} .$$
--   Then there exist $m^*\in\{1,\dots,K-1\}$ and $z^*\in(\phi_{m^*}/\phi_{m^*+1},1]$ such that
--   $$\frac{Q(m^*,z^*)}{R(m^*,z^*)}=\frac{B/s-l}{\gamma\bar\theta^*}.\tag{58}$$
--
--   The pair $(m^*,z^*)$ fixes the threshold and the constant level of the optimal allocation in Case 2.
--
--   **Formalization Note** The Case 2 condition, stated on p. 28 immediately before the claim, is written as a hypothesis.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 28, Claim 3, (58) (Case 2 condition stated on the same page)

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem claim_3 (P : Prog) (hP : P.Standing)
    (hlo : P.Q 1 1 / P.R 1 1 ≤ (P.B / P.s - P.l) / (P.gam * P.theta))
    (hhi : (P.B / P.s - P.l) / (P.gam * P.theta) < P.Q P.K 1 / P.R P.K 1) :
    ∃ m ∈ Finset.Icc 1 (P.K - 1), ∃ z : ℝ, P.phi m / P.phi (m + 1) < z ∧ z ≤ 1 ∧
      P.Q m z / P.R m z = (P.B / P.s - P.l) / (P.gam * P.theta) := by sorry

end PrivacyParadox.Alloc
