-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_gittins_policy_exists
-- name    : PandoraBO.Private20261023.gittins_policy_exists
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:48:48.157601+00:00
-- url     : https://prove2.me/theorems/f84bb81a-cf60-41b9-aef4-6d873bb71414
-- title:
--   Existence of a measurable positive-multiplier Gittins policy
-- statement:
--   For a finite independent-box instance and any strictly positive cost multiplier, there exists a measurable adaptive policy obeying the Gittins index rule. The first box has maximal reservation index. Subsequently the policy selects an unopened maximal-index box whenever its index exceeds the incumbent reward and otherwise stops. This result establishes existence only; optimality is a separate obligation.
-- source:
--   Auxiliary construction for Xie et al., Cost-aware Bayesian Optimization via the Pandora’s Box Gittins Index, author revised manuscript reviewed 23 October 2026, Appendix B.5, Lemmas 7–8 and Theorem 2. This result isolates the measurable-policy existence or policy-randomization step; it is not a verbatim numbered claim.

import Definitions.Def_PandoraBO_Model
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory PandoraBO
set_option autoImplicit false

theorem PandoraBO.Private20261023.gittins_policy_exists {n : ℕ} (M : PandoraBO.Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) :
    ∃ π : PandoraBO.Policy n, PandoraBO.isGittinsPolicy M multiplier π := by sorry
