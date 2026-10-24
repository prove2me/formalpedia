-- Prove2me | Theorems.Thm_OutpatientWalkIn_SmallCap_proposition_1_obs_exists
-- name    : OutpatientWalkIn.SmallCap.proposition_1_obs_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:35.215852+00:00
-- url     : https://prove2.me/theorems/43c976af-cb74-4fb5-ba17-0a286d29fa3d
-- title:
--   Proposition 1, p. 16 (observable setting, Online App. D.3, p. 10) — an observable equilibrium (δ, p_W, p_B) exists at every allocation 0 ≤ μ_S < μ
-- statement:
--   Assume the standing assumptions of the model (parameter signs, Assumptions 1 and 2). For every allocation of appointment hours $\mu_S$ with $0 \le \mu_S < \mu$, there is a strategy $(\delta,p_W,p_B)$ that is an equilibrium of the observable setting: conditions (6)–(10) hold with $C_G = 0$, the walk-in intensity is $(\lambda_E + p_W\lambda)/(\mu-\mu_S)$, and
--   $$p_W + p_B = \pi(\delta,\mu_S).$$
--
--   The observable setting is the paper's second-stage problem with $C_G = 0$, $\lambda_S = \lambda$ and $\lambda_W = 0$ (Lemma 4, Appendix D.3). This existence result makes the cost (Ob.P) well defined at every allocation.
--
--   **Formalization Note** Proposition 1 also describes the equilibrium in three regimes (SnB, SWB, SnW). That description needs $w^{-1}$ and the root $\delta^S_W$ of $C_D\delta = C_Ww((\pi(\delta,\mu_S)\lambda+\lambda_E)/\mu_W)$. This item states the existence part, which is what the goal uses. At $\mu_S = 0$, $\pi = 1$, and the item still asserts an equilibrium in which every strategic patient walks in or balks.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), p. 16, Proposition 1 (existence), specialised to the observable setting as in Online Appendix p. 10, D.3

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
import Definitions.Def_OutpatientWalkIn_SmallCap_Setting

namespace OutpatientWalkIn.SmallCap
theorem proposition_1_obs_exists (M : Model) (hM : M.Standing) (μS : ℝ) (hμS : μS ∈ Set.Ico 0 M.mu) :
    ∃ e : ObsStrategy, M.IsObsEq μS e := by sorry
end OutpatientWalkIn.SmallCap
