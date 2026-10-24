-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_policy_opening_regular
-- name    : PandoraBO.Private20261023.policy_opening_regular
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:16:00.284711+00:00
-- url     : https://prove2.me/theorems/9b1bf0e0-5b28-4f37-899d-d22370d16682
-- title:
--   Opening events are measurable and do not depend on the unopened reward
-- statement:
--   For each policy and box, the event that the box is opened is measurable. Changing only that box’s reward, while fixing all other rewards and the policy random seed, does not change whether the box is opened.
-- source:
--   Auxiliary lemma for Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5 and the finite independent-box policy model.

import Definitions.Def_PandoraBO_Model
open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

theorem PandoraBO.Private20261023.policy_opening_regular {n : ℕ} (π : PandoraBO.Policy n) (i : PandoraBO.Box n) :
    MeasurableSet {ω : PandoraBO.Outcome n |
      PandoraBO.wasOpened (PandoraBO.terminalHistory π ω) i} ∧
    (∀ (r r' : PandoraBO.Box n → ℝ) (u : ℝ),
      (∀ j, j ≠ i → r j = r' j) →
      (PandoraBO.wasOpened (PandoraBO.terminalHistory π (r, u)) i ↔
        PandoraBO.wasOpened (PandoraBO.terminalHistory π (r', u)) i))  := by sorry
