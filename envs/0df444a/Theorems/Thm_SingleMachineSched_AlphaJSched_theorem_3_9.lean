-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_theorem_3_9
-- name    : SingleMachineSched.AlphaJSched.theorem_3_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:21:26.329757+00:00
-- url     : https://prove2.me/theorems/1427e8e9-a8fa-4bfd-9b88-3b1e8d2526d6
-- title:
--   Theorem 3.9 — the random $(\alpha_j)$-schedule is within $c<1.6853$ of $Z_R$
-- statement:
--   Let $n$ jobs have integral processing times $p_j>0$, integral release dates $r_j\ge0$ and weights $w_j>0$, indexed in nonincreasing order of $w_j/p_j$. Let $\gamma\approx0.4835$ satisfy $0<\gamma<1$ and
--   $$\gamma+\ln(2-\gamma)=e^{-\gamma}\bigl((2-\gamma)e^{\gamma}-1\bigr),$$
--   and define $\delta=\gamma+\ln(2-\gamma)\approx0.8999$, $c=1+e^{-\gamma}/\delta$ and the density $g(\alpha)=(c-1)e^{\alpha}$ for $0<\alpha\le\delta$, $g(\alpha)=0$ otherwise. Then
--
--   1. $c<1.6853$;
--   2. whenever $\boldsymbol\alpha=(\alpha_1,\dots,\alpha_n)$ is a random vector whose coordinates each have density $g$ and are pairwise independent, the total weighted completion time of the random $(\alpha_j)$-schedule is integrable and
--   $$\mathbb E\Bigl[\sum_j w_j\,C^{\boldsymbol\alpha}_j\Bigr]\ \le\ c\cdot Z_R ,$$
--   where $Z_R$ is the optimal value of the mean busy time relaxation (R).
--
--   This is the main result of the paper: a randomized algorithm for $1|r_j|\sum w_jC_j$ with performance guarantee $1.6853$, and, since $Z_R$ is a lower bound on the optimum, a proof that (R), and the time-indexed relaxation (D) with the same value, is within a factor $1.6853$ of the optimum.
--
--   **Formalization Note.** The random vector is any probability measure on $\mathbb R^n$ whose coordinate marginals all equal the measure with density $g$ and whose coordinates are pairwise independent; the product measure is one such measure, and the claim is for all of them, as the paper's "pairwise independently" requires. The bound is stated against $Z_R$ as defined from (R); the paper writes $Z_D=Z_R$, and that equality is Corollary 2.6, the goal of the first mission of the series. $\gamma$ is any solution in $(0,1)$ of the equation; the paper calls it the unique one, and uniqueness is not asserted here. The running time and the derandomization of the algorithm are not formalized.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, p. 185, Theorem 3.9

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaPoints
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaJSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_DensityG

namespace SingleMachineSched.AlphaJSched

open MeasureTheory ProbabilityTheory

/-- Theorem 3.9: let `γ ∈ (0, 1)` solve `γ + ln(2 − γ) = e^{−γ}((2 − γ)e^γ − 1)`, and
`δ = γ + ln(2 − γ)`, `c = 1 + e^{−γ}/δ`. Then `c < 1.6853`, and whenever the `α_j` are chosen
pairwise independently, each with density `g`, the expected weighted completion time of the
random `(α_j)`-schedule is finite and at most `c · Z_R`. -/
theorem theorem_3_9 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j)
    (γ : ℝ) (hγ : 0 < γ ∧ γ < 1 ∧
      γ + Real.log (2 - γ) = Real.exp (-γ) * ((2 - γ) * Real.exp γ - 1)) :
    cConst γ < 1.6853 ∧
      ∀ μ : Measure (Fin n → ℝ), IsProbabilityMeasure μ →
        (∀ j, μ.map (fun a => a j) = gMeasure γ) →
        (∀ j k, j ≠ k → IndepFun (fun a => a j) (fun a => a k) μ) →
        Integrable (fun a => ∑ j, w j * (alphaCompletion p r a j : ℝ)) μ ∧
          ∫ a, ∑ j, w j * (alphaCompletion p r a j : ℝ) ∂μ ≤ cConst γ * Shared.zR p r w := by sorry

end SingleMachineSched.AlphaJSched
