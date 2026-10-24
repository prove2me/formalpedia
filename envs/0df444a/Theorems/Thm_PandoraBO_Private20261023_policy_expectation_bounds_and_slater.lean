-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_policy_expectation_bounds_and_slater
-- name    : PandoraBO.Private20261023.policy_expectation_bounds_and_slater
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:28:45.559569+00:00
-- url     : https://prove2.me/theorems/b5e4e191-c21a-413c-b7e3-69494651d7a9
-- title:
--   Uniform policy expectation bounds and a single-box feasibility witness
-- statement:
--   For every finite independent-box instance with integrable real rewards and positive deterministic opening costs, there are finite nonnegative constants that bound the absolute expected reward and absolute expected cost of every policy. Moreover, for each box there exists a policy whose expected cost equals that box’s cost. These facts supply finite real dual envelopes and a strictly feasible policy whenever at least one box costs less than the expected budget.
-- source:
--   Foundational consequences of the finite-box policy model supporting Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5, Lemma 6 and equations (38)–(39). The uniform bounds and explicit one-box policy are isolated here for Lean formalization.

import Definitions.Def_PandoraBO_Model
set_option autoImplicit false

theorem PandoraBO.Private20261023.policy_expectation_bounds_and_slater {n : ℕ} (M : PandoraBO.Instance n) :
    (∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧
      ∀ π : PandoraBO.Policy n,
        |PandoraBO.expectedReward M π| ≤ R ∧ |PandoraBO.expectedCost M π| ≤ C) ∧
    (∀ i : PandoraBO.Box n, ∃ π : PandoraBO.Policy n,
      PandoraBO.expectedCost M π = M.cost i) := by sorry
