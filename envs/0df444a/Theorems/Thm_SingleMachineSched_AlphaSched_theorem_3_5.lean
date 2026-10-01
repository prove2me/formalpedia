-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaSched_theorem_3_5
-- name    : SingleMachineSched.AlphaSched.theorem_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:14:52.598969+00:00
-- url     : https://prove2.me/theorems/6d40e561-e721-4deb-857b-d9989b07a87f
-- title:
--   Theorem 3.5 — the random $\alpha$-schedule is within $c < 1.7451$ of $Z_R$
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$, integral release dates $r_j \ge 0$ and weights $w_j > 0$, indexed so that $w_1/p_1 \ge \cdots \ge w_n/p_n$. Let $0 < \gamma < 1$ satisfy
--
--   $$1 - \frac{\gamma^2}{1 + \gamma} = \gamma + \ln(1 + \gamma)$$
--
--   ($\gamma \approx 0.4675$), and let
--
--   $$c = \frac{1+\gamma}{1+\gamma-e^{-\gamma}}, \qquad \delta = 1 - \frac{\gamma^2}{1+\gamma} \approx 0.8511 .$$
--
--   Draw a single $\alpha$ with density $f(\alpha) = (c-1)e^\alpha$ on $(0, \delta]$ and $0$ elsewhere, and let $C^\alpha_j$ be the completion time of job $j$ in the $\alpha$-schedule, which processes the jobs nonpreemptively, as early as possible, in nondecreasing order of their $\alpha$-points in the LP schedule. Then:
--
--   1. $c < 1.7451$;
--   2. the expected objective value $\mathbb E_f\big[\sum_j w_j C^\alpha_j\big]$ is finite, and
--   $$\mathbb E_f\Big[\sum_{j} w_j C^\alpha_j\Big] \le c \cdot Z_R ,$$
--   where $Z_R$ is the optimal value of the mean busy time relaxation (R).
--
--   Since $Z_R$ is a lower bound on the optimal value of the scheduling problem, the random $\alpha$-schedule is a randomized $1.7451$-approximation for minimizing $\sum_j w_j C_j$ on one machine with release dates.
--
--   **Formalization Note** The paper states the bound against $Z_D = Z_R$; this statement uses $Z_R$ as defined from (R), and the equality with $Z_D$ is not part of it. The expectation is the Lebesgue integral against the law $f(\alpha)\,d\alpha$, and its finiteness is asserted explicitly. $\gamma$ is any solution of the equation in $(0, 1)$; the paper's "unique" is not asserted. The completion times are those of the $(\alpha_j)$-schedule with all $\alpha_j$ equal to $\alpha$.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 183, Theorem 3.5

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaSched_AlphaSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR
import Definitions.Def_SingleMachineSched_AlphaSched_Density

namespace SingleMachineSched.AlphaSched

open MeasureTheory

/-- Theorem 3.5 (Goemans et al. 2002, p. 183): let `γ ∈ (0, 1)` solve
`1 - γ²/(1+γ) = γ + ln(1+γ)`, `c = (1+γ)/(1+γ-e^{-γ})` and `δ = 1 - γ²/(1+γ)`. Then
`c < 1.7451`, and if `α` has density `f(α) = (c - 1) e^α` on `(0, δ]` (and `0` elsewhere), the
expected weighted completion time of the `α`-schedule (all `α_j = α`) is finite and at most
`c · Z_R`. Jobs are indexed by nonincreasing `w_j / p_j`, and weights are positive. -/
theorem theorem_3_5 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j)
    (γ : ℝ) (hγ : 0 < γ ∧ γ < 1 ∧ 1 - γ ^ 2 / (1 + γ) = γ + Real.log (1 + γ)) :
    cConst γ < 1.7451 ∧
      Integrable (fun a : ℝ => ∑ j, w j * alphaCompletion p r (fun _ => a) j) (fMeasure γ) ∧
      ∫ a, ∑ j, w j * alphaCompletion p r (fun _ => a) j ∂(fMeasure γ) ≤
        cConst γ * Shared.zR p r w := by sorry

end SingleMachineSched.AlphaSched
