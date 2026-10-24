-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_pathwise_capped_reward_upper_bound
-- name    : PandoraBO.Private20261023.pathwise_capped_reward_upper_bound
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:08:25.574811+00:00
-- url     : https://prove2.me/theorems/d4dfa06b-db29-4d0f-8b69-c2e4c18451e5
-- title:
--   Pathwise capped-reward upper bound for an adaptive policy
-- statement:
--   For any finite policy, outcome, and real vector of thresholds, the terminal reward is at most the maximum of all rewards capped at their thresholds plus the sum, over opened slots, of the positive reward excess above the corresponding threshold. This pathwise statement does not assume optimality or a reservation-root equation.
-- source:
--   Finite policy and capped-reward foundations supporting Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5, Lemma 7 and equation (42). These pathwise auxiliary statements are isolated for the Lean proof rather than separately numbered in the paper.

import Definitions.Def_PandoraBO_Model
open MeasureTheory PandoraBO
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

theorem PandoraBO.Private20261023.pathwise_capped_reward_upper_bound {n : ℕ} (π : Policy n) (ω : Outcome n) (z : Box n → ℝ) :
    terminalReward π ω ≤
      fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
        ∑ k : Fin (n + 1), if occupied (terminalHistory π ω) k then
          max (observedReward (terminalHistory π ω) k -
            z (observedBox (terminalHistory π ω) k)) 0 else 0 := by sorry
