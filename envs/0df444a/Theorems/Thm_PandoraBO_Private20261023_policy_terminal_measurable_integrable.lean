-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_policy_terminal_measurable_integrable
-- name    : PandoraBO.Private20261023.policy_terminal_measurable_integrable
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:48:46.657541+00:00
-- url     : https://prove2.me/theorems/3e73d346-a983-42a6-95ce-e42bf28839ac
-- title:
--   Measurability and integrability of policy terminal reward and cost
-- statement:
--   For every policy in the finite independent-box model, terminal reward and terminal opening cost are measurable and integrable under the joint law of all box rewards and the independent random seed. Policies are measurable and adaptive as specified by the model; no continuity or atomlessness assumption on reward distributions is added. This ensures the expectations used in the budgeted search problem are ordinary finite expectations.
-- source:
--   Probability foundations of the finite-box policy model underlying Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5 (Theorem 2 proof). This auxiliary measurability/integrability result is isolated for formalization, not a separately numbered source lemma.

import Definitions.Def_PandoraBO_Model
open MeasureTheory
set_option autoImplicit false

theorem PandoraBO.Private20261023.policy_terminal_measurable_integrable {n : ℕ} (M : PandoraBO.Instance n) (π : PandoraBO.Policy n) :
    Measurable (PandoraBO.terminalReward π) ∧
    Measurable (PandoraBO.terminalCost M π) ∧
    Integrable (PandoraBO.terminalReward π) (PandoraBO.jointLaw M) ∧
    Integrable (PandoraBO.terminalCost M π) (PandoraBO.jointLaw M) := by sorry
