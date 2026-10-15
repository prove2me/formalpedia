-- Prove2me | Theorems.Thm_OutpatientWalkIn_SmallCap_lemma_E_5_1
-- name    : OutpatientWalkIn.SmallCap.lemma_E_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:33.02706+00:00
-- url     : https://prove2.me/theorems/79e79eab-ef49-430e-a1d0-2105ec9fab9a
-- title:
--   Lemma E.5 (1), Online App. p. 26 — at a fixed allocation, λ^o_S(d̄^u) ≥ λ^u_S makes the observable setting cost no more
-- statement:
--   Assume the standing assumptions of the model and fix an allocation $0 \le \mu_S < \mu$, with $\mu_W = \mu - \mu_S$. Let $(\lambda^u_S,\lambda^u_W,\lambda^u_B)$ be an unobservable equilibrium at $\mu_S$, with expected delay
--   $$\bar d^u = \frac{\lambda^u_S}{2\mu_S(\mu_S-\lambda^u_S)}.$$
--   Let $(\delta, p_W, p_B)$ be any observable equilibrium at $\mu_S$. Write $\lambda^o_S(\delta') = \lambda[1-\pi(\delta',\mu_S)]$ for the scheduling rate when every strategic patient uses the threshold $\delta'$. If
--   $$\lambda^o_S(\bar d^u) \ge \lambda^u_S,$$
--   then the observable setting costs no more than the unobservable one at this allocation:
--   $$C_L p_B\lambda + C_O\,o\Big(\frac{p_W\lambda+\lambda_E}{\mu_W}\Big) \;\le\; C_L\lambda^u_B + C_O\,o\Big(\frac{\lambda^u_W+\lambda_E}{\mu_W}\Big).$$
--
--   This is the same-allocation comparison that the proof of Theorem 2(1) applies at an unobservable allocation.
--
--   **Formalization Note** "Costs less" is defined on p. 26 as "no more", so the conclusion is $\le$. Part 2 of Lemma E.5 is not stated. The lemma's parameter list omits $C_L, C_O$; they enter through the costs, with $C_L, C_O \ge 0$ from the standing assumptions. At $\mu_S = 0$ the convention $\pi(\cdot,0) = 1$ applies and $\bar d^u = 0$ (Lean's $0/0$), and the hypothesis reads $0 \ge 0$. The conclusion holds for every observable equilibrium, not a chosen one.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix p. 26, Lemma E.5 (1) and the definitions of d̄^u, λ^u_S, λ^o_S(δ) preceding it

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
import Definitions.Def_OutpatientWalkIn_SmallCap_Setting

namespace OutpatientWalkIn.SmallCap
theorem lemma_E_5_1 (M : Model) (hM : M.Standing) (μS : ℝ) (hμS : μS ∈ Set.Ico 0 M.mu)
    (u : UnobsStrategy) (hu : M.IsUnobsEq μS u) (e : ObsStrategy) (he : M.IsObsEq μS e)
    (hrate : M.lam * (1 - blockProb M.lam (dbar μS u.lamS) μS) ≥ u.lamS) :
    M.obsCost μS e ≤ M.unobsCost μS u := by sorry
end OutpatientWalkIn.SmallCap
