-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_gittins_pathwise_capped_reward_identity
-- name    : PandoraBO.Private20261023.gittins_pathwise_capped_reward_identity
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:16:59.400055+00:00
-- url     : https://prove2.me/theorems/9dbed694-cd53-41a4-b700-48a82ac8b4c1
-- title:
--   Pathwise capped-reward identity for a Gittins policy
-- statement:
--   For every outcome, a finite positive-multiplier Gittins policy achieves the maximum of the rewards capped at their reservation indices plus the sum of the opened positive reward excesses. All tie choices allowed by the Gittins policy definition are included. The first opening is mandatory, and rewards may be negative.
-- source:
--   Finite policy and capped-reward foundations supporting Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5, capped-reward identity in equation (42).

import Definitions.Def_PandoraBO_Model
open MeasureTheory PandoraBO
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

theorem PandoraBO.Private20261023.gittins_pathwise_capped_reward_identity {n : ℕ} (M : Instance n) (multiplier : ℝ) (hpos : 0 < multiplier)
    (z : Box n → ℝ) (hz : reservationIndices M multiplier z) (π : Policy n)
    (hπ : isGittinsPolicy M multiplier π) (ω : Outcome n) :
    terminalReward π ω =
      fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
        ∑ k : Fin (n + 1), if occupied (terminalHistory π ω) k then
          max (observedReward (terminalHistory π ω) k -
            z (observedBox (terminalHistory π ω) k)) 0 else 0  := by sorry
