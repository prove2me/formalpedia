-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_policy_capped_integrability_and_excess
-- name    : PandoraBO.Private20261023.policy_capped_integrability_and_excess
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:07.799563+00:00
-- url     : https://prove2.me/theorems/b8a173d7-5fae-44a4-8c67-5346ba10d616
-- title:
--   Capped payoff integrability and expected opened-box excess
-- statement:
--   The maximum of capped box rewards and the total positive excess over reservation indices among opened boxes are integrable. Their expected total opened excess equals the multiplier times expected opening cost. The equality uses the independent reward laws, nonanticipative policies, distinct openings, and the reservation-root equations.
-- source:
--   Auxiliary expectation identity in the capped-reward proof of Weitzman optimality for the finite independent Pandora model.

import Definitions.Def_PandoraBO_Model
open MeasureTheory
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

theorem PandoraBO.Private20261023.policy_capped_integrability_and_excess {n : ℕ} (M : PandoraBO.Instance n) (multiplier : ℝ)
    (z : PandoraBO.Box n → ℝ) (hz : PandoraBO.reservationIndices M multiplier z)
    (π : PandoraBO.Policy n) :
    Integrable (fun ω : PandoraBO.Outcome n =>
      PandoraBO.fullInformationPayoff (fun i => min (ω.1 i) (z i))) (PandoraBO.jointLaw M) ∧
    Integrable (fun ω : PandoraBO.Outcome n => ∑ k : Fin (n + 1),
      if PandoraBO.occupied (PandoraBO.terminalHistory π ω) k then
        max (PandoraBO.observedReward (PandoraBO.terminalHistory π ω) k -
          z (PandoraBO.observedBox (PandoraBO.terminalHistory π ω) k)) 0 else 0)
      (PandoraBO.jointLaw M) ∧
    (∫ ω : PandoraBO.Outcome n, ∑ k : Fin (n + 1),
      if PandoraBO.occupied (PandoraBO.terminalHistory π ω) k then
        max (PandoraBO.observedReward (PandoraBO.terminalHistory π ω) k -
          z (PandoraBO.observedBox (PandoraBO.terminalHistory π ω) k)) 0 else 0
      ∂PandoraBO.jointLaw M) = multiplier * PandoraBO.expectedCost M π := by sorry
