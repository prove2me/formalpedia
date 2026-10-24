-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_policy_expectations_converge_of_eventual_decisions
-- name    : PandoraBO.Private20261023.policy_expectations_converge_of_eventual_decisions
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:18:50.637707+00:00
-- url     : https://prove2.me/theorems/595b5a03-fa16-48b3-b910-72e9c570a1b8
-- title:
--   Policy expectations converge when each decision eventually agrees
-- statement:
--   If each first decision and each decision at a fixed history eventually agrees with a limiting policy, each finite rollout eventually agrees pointwise, and expected reward and cost converge. No regularity of the reward distributions beyond the original integrability assumptions is needed.
-- source:
--   Auxiliary finite policy rollout and dominated convergence lemma for the author revised Pandora Bayesian optimization manuscript.

import Definitions.Def_PandoraBO_Model
open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

theorem PandoraBO.Private20261023.policy_expectations_converge_of_eventual_decisions {n : ℕ} (M : PandoraBO.Instance n)
    (policies : ℕ → PandoraBO.Policy n) (π : PandoraBO.Policy n)
    (hfirst : ∀ u : ℝ, ∀ᶠ k in atTop, (policies k).first u = π.first u)
    (hnext : ∀ h : PandoraBO.History n, ∀ u : ℝ,
      ∀ᶠ k in atTop, (policies k).next (h, u) = π.next (h, u)) :
    (∀ ω : PandoraBO.Outcome n, ∀ᶠ k in atTop,
      PandoraBO.terminalHistory (policies k) ω = PandoraBO.terminalHistory π ω) ∧
    Tendsto (fun k => PandoraBO.expectedCost M (policies k)) atTop
      (nhds (PandoraBO.expectedCost M π)) ∧
    Tendsto (fun k => PandoraBO.expectedReward M (policies k)) atTop
      (nhds (PandoraBO.expectedReward M π))  := by sorry
