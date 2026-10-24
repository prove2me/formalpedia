-- Prove2me | Theorems.Thm_OutpatientWalkIn_Triage_scheduling_rate_bound
-- name    : OutpatientWalkIn.Triage.scheduling_rate_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:56.780979+00:00
-- url     : https://prove2.me/theorems/16c76ca9-de98-43d9-bb08-019d4f06e9c2
-- title:
--   Proof of Proposition 6 (1), Online App. p. 36 — the strategic scheduling rate is at most λ[1 − π(R/C_D, µ_S)]
-- statement:
--   Under the standing assumptions, let $\mu_S\in[0,\mu)$ and let $(\delta,p_W,p_B)$ be an observable equilibrium at $\mu_S$. The rate at which strategic patients schedule is $\lambda^{s}_S=\lambda\,(1-\pi(\delta,\mu_S))$, and
--   $$\lambda\,\big(1-\pi(\delta,\mu_S)\big)\le\lambda\,\Big(1-\pi\Big(\frac{R}{C_D},\mu_S\Big)\Big).$$
--
--   In words: no equilibrium threshold exceeds $R/C_D$, the delay at which scheduling is worth nothing, so the strategic model never schedules more patients than the triage model at the same allocation. This is the first inequality in the proof of part 1 of Proposition 6.
--
--   **Formalization Note** The paper states the bound in the regimes SnW and SWB; it holds in every regime (with equality in SnB), and is posed without the regime hypothesis.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix p. 36, proof of Proposition 6 (1)

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting

namespace OutpatientWalkIn.Triage

theorem scheduling_rate_bound (M : Model) (hM : M.Standing) :
    ∀ μS ∈ Set.Ico 0 M.mu, ∀ e : ObsStrategy, M.IsObsEq μS e →
      M.lam * (1 - blockProb M.lam e.δ μS) ≤ M.lam * (1 - blockProb M.lam (M.R / M.CD) μS) := by sorry

end OutpatientWalkIn.Triage
