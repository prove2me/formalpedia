-- Prove2me | Theorems.Thm_OutpatientWalkIn_SmallCap_theorem_2_1
-- name    : OutpatientWalkIn.SmallCap.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:29.047161+00:00
-- url     : https://prove2.me/theorems/fd7283cf-5924-4818-874d-fa48057a3d88
-- title:
--   Theorem 2 (1), p. 26 — for μ ≤ √(λC_D/(2R)) the observable setting costs no more than the unobservable one
-- statement:
--   Consider the observable and unobservable settings with the same parameters $(\lambda,\lambda_E,R,C_D,C_W,C_L,C_O,\mu)$, in-clinic wait function $w$ and overtime function $o$, under the standing assumptions (parameter signs, Assumptions 1 and 2). Suppose the total daily capacity is small:
--   $$\mu \;\le\; \sqrt{\frac{\lambda C_D}{2R}} .$$
--   Then for every allocation $0 \le \mu_S < \mu$ and every unobservable equilibrium $u = (\lambda_S,\lambda_W,\lambda_B)$ at $\mu_S$, there is an allocation $0 \le \mu'_S < \mu$ such that
--
--   1. an observable equilibrium exists at $\mu'_S$, and
--   2. every observable equilibrium $(\delta,p_W,p_B)$ at $\mu'_S$ costs no more than $u$:
--   $$C_L p_B\lambda + C_O\,o\Big(\frac{p_W\lambda+\lambda_E}{\mu-\mu'_S}\Big) \;\le\; C_L\lambda_B + C_O\,o\Big(\frac{\lambda_W+\lambda_E}{\mu-\mu_S}\Big).$$
--
--   In words: when capacity is short, telling patients the exact appointment delay (real-time scheduling) is at least as good for the provider as letting them decide on the expected delay. The best cost achievable in the observable setting is at most the best cost achievable in the unobservable setting.
--
--   **Formalization Note** The printed statement says "when $\mu$ is sufficiently small". The explicit threshold $\sqrt{\lambda C_D/(2R)}$ is the one the paper's proof establishes (Online Appendix p. 28), and stating it is stronger than the bare existence of a threshold; the literal form would read $\exists \mu_0 > 0$ such that the conclusion holds whenever $\mu \le \mu_0$, with $\mu_0$ depending on every parameter except $\mu$. "Costs less" means "no more" (p. 26). The paper's proof starts from "the optimal allocation" of (Un.P), whose existence it does not prove. The $\forall$–$\exists$ form says $\inf(\text{Ob.P}) \le \inf(\text{Un.P})$ without assuming that either optimum is attained, and it does not let the observable side pick a favourable equilibrium. Allocations range over $0 \le \mu_S < \mu$ so that walk-in intensities are defined. Part 2 of Theorem 2 is not stated.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), p. 26, Theorem 2 (1); threshold μ ≤ √(λC_D/(2R)) from the proof, Online Appendix p. 28

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
import Definitions.Def_OutpatientWalkIn_SmallCap_Setting

namespace OutpatientWalkIn.SmallCap
theorem theorem_2_1 (M : Model) (hM : M.Standing) (hμ : M.mu ≤ Real.sqrt (M.lam * M.CD / (2 * M.R)))
    (μS : ℝ) (hμS : μS ∈ Set.Ico 0 M.mu) (u : UnobsStrategy) (hu : M.IsUnobsEq μS u) :
    ∃ μS' ∈ Set.Ico 0 M.mu, (∃ e : ObsStrategy, M.IsObsEq μS' e) ∧
      ∀ e : ObsStrategy, M.IsObsEq μS' e → M.obsCost μS' e ≤ M.unobsCost μS u := by sorry
end OutpatientWalkIn.SmallCap
