-- Prove2me | Theorems.Thm_ParetoNCSched_Supplement_theorem_1_3
-- name    : ParetoNCSched.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:44:01.719782+00:00
-- url     : https://prove2.me/theorems/24953721-25e7-4535-be2d-cdcffdc881a2
-- title:
--   Theorem 1.3 — $\mathrm{RT}_\rho$ is $(1+\varepsilon(\rho))$-consistent and $(2+\rho)$-robust, strictly below the deterministic frontier
-- statement:
--   Consider non-clairvoyant scheduling of $n$ jobs on one machine with predicted sizes $y\in(0,\infty)^n$, minimizing the total completion time. Let $\rho_0=(\sqrt{10}-3)/2\approx0.081$ and, for $\rho>0$,
--
--   $$\varepsilon(\rho)=\int_0^1\frac{v^2\,dv}{v^2+3\rho v+\rho^2}.$$
--
--   The randomized two-stage algorithm $\mathrm{RT}_\rho$ draws $V$ uniformly in $(0,1)$, sets $B=V^2/(V^2+3\rho V+\rho^2)$ and $L=w_y^{-1}(B)$, runs Round-Robin until the common elapsed time of the unfinished jobs reaches $L$, then the unfinished jobs one at a time in increasing order of $y_j$, and at the first mismatch (a job completing with elapsed time $\ne y_j$, or reaching $y_j$ without completing) switches to Round-Robin on the unfinished jobs of smallest elapsed time. Its consistency and robustness use its expected total completion time, against an oblivious adversary. Then:
--
--   1. for every $\rho\ge\rho_0$, $\mathrm{RT}_\rho$ is $(1+\varepsilon(\rho))$-consistent: $\mathrm{cons}(\mathrm{RT}_\rho)\le1+\varepsilon(\rho)$;
--   2. for every $\rho\ge\rho_0$, $\mathrm{RT}_\rho$ is $(2+\rho)$-robust: $\mathrm{rob}(\mathrm{RT}_\rho)\le2+\rho$;
--   3. for every $\rho\ge\rho_0$,
--   $$2+\rho<R^*\big(1+\varepsilon(\rho)\big),$$
--   where $R^*(c_0)$ is the infimum of $\mathrm{rob}(A)$ over all deterministic algorithms $A$, with predicted orders or with predicted sizes, with $\mathrm{cons}(A)\le c_0$;
--   4. at consistency $1+\varepsilon$ its robustness is $(3\varepsilon)^{-1/2}+O(1)$ as $\varepsilon\to0$: there are $C$ and $\varepsilon_1>0$ such that $\left|2+\rho-(3\varepsilon(\rho))^{-1/2}\right|\le C$ for every $\rho\ge\rho_0$ with $\varepsilon(\rho)<\varepsilon_1$.
--
--   With predicted sizes, randomization therefore strictly beats the Pareto-optimal frontier of deterministic algorithms, and near consistency $1$ it improves the leading constant $\varepsilon^{-1/2}$ of $R^*(1+\varepsilon)$ by a factor $\sqrt3$.
--
--   **Formalization Note** Deterministic algorithms, $\mathrm{cons}$, $\mathrm{rob}$ and $R^*$ are those of Appendix A, all in $[0,\infty]$. The run of $\mathrm{RT}_L$ is an explicit event-driven iteration, and the expectation is the Lebesgue integral over $V\in(0,1)$.
--
--   Differences from the source:
--   - reading: At consistency 1 + ε, its robustness is (3ε)^{−1/2} + O(1) as ε → 0 → ∃ C, ∃ ε₁ > 0, ∀ ρ ≥ ρ₀, ε(ρ) < ε₁ → |2 + ρ − (3ε(ρ))^{−1/2}| ≤ C; reason: the proof (p.44) reads it as 'at consistency 1+ε, RTρ has ρ = (3ε)^{−1/2}+O(1)': the robustness guarantee 2 + ρ of RTρ at the ρ with ε(ρ) = ε, two-sided; the paper proves only the upper bound 2 + ρ on rob(RTρ), so its exact value is not claimed
--   - reading: Algorithm 2, line 4: Round-Robin on the unfinished jobs of smallest elapsed time → levelling: the minimal-elapsed unfinished jobs are served equally, a job joins the served group when the group's elapsed time reaches its own; reason: the paper gives no explicit rate function for this step; levelling is the rate function its description and the proof (p.42: the jobs of Q 'are served first', equal elapsed times 'until the shorter one completes') use
--   - encoding: RTρ, a randomized algorithm running the deterministic algorithm RT_L → the run of RT_L written as an explicit event-driven iteration (rtRun, rtRate) on the sizes p and predictions y, the sizes entering only through completions; reason: the same run, written directly instead of as a DetAlg instance
--   - encoding: E[·] over V uniform in (0,1) → Lebesgue lower integral ∫⁻ over V ∈ Ioo 0 1 in ℝ≥0∞; reason: Ioo 0 1 has measure 1; equals the expectation when the cost is measurable in V; no integrability side condition
--   - encoding: L = w_y^{−1}(B) → inf {s ≥ 0 : w_y(s) ≥ B}; reason: w_y is continuous and strictly increasing on [0, y_n] from 0 to 1 and B ∈ (0,1), so this is the unique solution
--   - encoding: R*(c₀): infimum of rob(A) over deterministic A with cons(A) ≤ c₀, in either prediction model; 2 + ρ < R*(1 + ε(ρ)) → Rstar: one infimum in ℝ≥0∞ over the union of DetAlg orderModel and DetAlg sizeModel; the strict inequality in ℝ≥0∞; reason: Lean convention; same value (an empty infimum is ⊤)
--   - encoding: cons, rob of a randomized algorithm with the expected total completion time; ρ₀ = (√10−3)/2 ≈ 0.081 → consOf/robOf of the size model applied to rtCost ρ, in ℝ≥0∞; ρ₀ exact; reason: Lean convention; same values
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem 1.3, p.4; Algorithm 2, p.13; Appendix H, pp.39–44; R*, Appendix F, p.36

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_rtCost
import Definitions.Def_ParetoNCSched_Supplement_Rstar
import Definitions.Def_ParetoNCSched_Supplement_rho0
import Definitions.Def_ParetoNCSched_Supplement_epsRho
open scoped ENNReal

namespace ParetoNCSched.Supplement

/-- **Theorem 1.3 (Randomization).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 1.1, Theorem 1.3, p.4 (proof: Appendix H,
pp.39–44): "For every ρ ≥ ρ0 = (√10−3)/2 ≈ 0.081, RTρ is (1 + ε(ρ))-consistent and
(2 + ρ)-robust, where ε(ρ) = ∫₀¹ v² dv/(v²+3ρv+ρ²), and 2 + ρ < R∗(1 + ε(ρ)). At consistency
1 + ε, its robustness is (3ε)^{−1/2} + O(1) as ε → 0."

**Formalization Note.**
* `RTρ` (Algorithm 2) works with predicted sizes; its expected total completion time over
  `V ~ U(0, 1)` is `rtCost ρ`, and `cons`/`rob` are `consOf`/`robOf` of the size model with that
  expected cost (oblivious adversary).
* `R*` is `Rstar`, the infimum of `rob(A)` over the deterministic algorithms of Appendix A with
  `cons(A) ≤ 1 + ε(ρ)`, in either prediction model; the inequality is strict, in `ℝ≥0∞`.
* The last sentence is read, as in its proof (p.44: "at consistency 1+ε, RTρ has
  ρ = (3ε)^{−1/2} + O(1)"), as a two-sided bounded difference between the robustness guarantee
  `2 + ρ` and `(3ε(ρ))^{−1/2}` for every `ρ ≥ ρ₀` with `ε(ρ)` small. -/
theorem theorem_1_3 :
    (∀ ρ : ℝ, rho0 ≤ ρ →
      consOf sizeModel (fun _ p y => rtCost ρ p y) ≤ ENNReal.ofReal (1 + epsRho ρ) ∧
      robOf sizeModel (fun _ p y => rtCost ρ p y) ≤ ENNReal.ofReal (2 + ρ) ∧
      ENNReal.ofReal (2 + ρ) < Rstar (ENNReal.ofReal (1 + epsRho ρ))) ∧
    (∃ C ε₁ : ℝ, 0 < ε₁ ∧ ∀ ρ : ℝ, rho0 ≤ ρ → epsRho ρ < ε₁ →
      |2 + ρ - (3 * epsRho ρ) ^ (-(1 / 2 : ℝ))| ≤ C) := by sorry

end ParetoNCSched.Supplement
