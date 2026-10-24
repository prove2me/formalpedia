-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_gittins_policy_mixture
-- name    : PandoraBO.Private20261023.gittins_policy_mixture
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:48:50.909015+00:00
-- url     : https://prove2.me/theorems/dbff0473-4841-4313-ab95-f5dcab07b4cb
-- title:
--   Randomized mixtures of Gittins policies interpolate reward and cost
-- statement:
--   Two Gittins policies at the same positive multiplier can be mixed with any weight a in [0,1]. There exists a Gittins policy whose expected cost and expected reward are the corresponding weighted averages. No continuity or atomlessness assumption on reward laws is needed.
-- source:
--   Auxiliary construction for Xie et al., Cost-aware Bayesian Optimization via the Pandora’s Box Gittins Index, author revised manuscript reviewed 23 October 2026, Appendix B.5, Lemmas 7–8 and Theorem 2. This result isolates the measurable-policy existence or policy-randomization step; it is not a verbatim numbered claim.

import Definitions.Def_PandoraBO_Model
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory PandoraBO
set_option autoImplicit false

theorem PandoraBO.Private20261023.gittins_policy_mixture {n : ℕ} (M : Instance n) (multiplier : ℝ)
    (hpos : 0 < multiplier) (π ρ : Policy n)
    (hπ : isGittinsPolicy M multiplier π) (hρ : isGittinsPolicy M multiplier ρ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ σ : Policy n, isGittinsPolicy M multiplier σ ∧
      expectedCost M σ = a * expectedCost M π + (1 - a) * expectedCost M ρ ∧
      expectedReward M σ = a * expectedReward M π + (1 - a) * expectedReward M ρ := by sorry
