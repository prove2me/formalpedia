-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_proposition_2
-- name    : TeamDiversity.WageGap.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:26.649149+00:00
-- url     : https://prove2.me/theorems/6e78dfa1-cf0c-4c43-a002-5dce0e0d8035
-- title:
--   Proposition 2, p. 19 — if f_s(0)/f_s(2) > f_d(0)/f_d(2), E[w_s**] − E[w_d*] falls on [0, δ^C], rises beyond; diverse optimal iff S < S*(δ); S* increasing for δ > δ^C
-- statement:
--   Assume the standing assumptions of the model and
--   $$\frac{f_s(0)}{f_s(2)} > \frac{f_d(0)}{f_d(2)},$$
--   the condition of Lemma 4 under which $E[w_s^{**}] - E[w_d^*] > 0$. For each $\delta \in [0,1]$ let $w_s^{**}(\delta)$ be the least feasible wage of the specialized program ((IR), (M-IC), (No-cycling)) and $w_d^*(\delta)$ the least feasible wage of the diverse program ((IR), (M-IC)). Write $G(\delta) = E[w_s^{**}] - E[w_d^*] = f_s(2)w_s^{**}(\delta) - f_d(2)w_d^*(\delta)$ and $S^*(\delta) = \frac{2}{\Delta}G(\delta)$ with $\Delta = f_s(2)-f_d(2)$. Then:
--
--   1. $G$ is strictly decreasing on $[0,\delta^C]$;
--   2. $G$ is strictly increasing on $(\delta^C, 1]$;
--   3. for every $\delta \in [0,1]$ and every $S > 0$: if $S < S^*(\delta)$ then $V_d > V_s$ (diverse teams are optimal), and if $S \ge S^*(\delta)$ then $V_s \ge V_d$ (specialized teams are optimal);
--   4. for every $\delta \in (\delta^C, 1)$, $S^*$ is differentiable at $\delta$ and
--   $$\frac{\partial S^*(\delta)}{\partial \delta} > 0.$$
--
--   This is the paper's main result: the cost disadvantage of specialized teams falls as long as mutual monitoring is the binding incentive, then rises once collusion must be deterred, so the range of output values for which diverse teams are optimal widens with patience beyond $\delta^C$.
--
--   **Formalization Note** The hypothesis "the conditions ensuring $E[w_s^{**}] - E[w_d^*] > 0$ (characterized in Lemma 4)" is pinned down as Lemma 4's explicit condition $f_s(0)/f_s(2) > f_d(0)/f_d(2)$; a bare positivity hypothesis is not used. "Monotone" is read as strict. "Specialized teams are optimal otherwise" is read weakly, since at $S = S^*(\delta)$ both compositions tie. The derivative clause uses Mathlib's `deriv`, which is $0$ at a point of non-differentiability, so the clause also asserts differentiability.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), p. 19 (PDF 20), Proposition 2

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Proposition 2, p. 19: under `f_s(0)/f_s(2) > f_d(0)/f_d(2)` (the condition of Lemma 4 making
`E[w_s**] − E[w_d*] > 0`), the gap `E[w_s**] − E[w_d*]` is strictly decreasing for `δ ≤ δ^C` and
strictly increasing for `δ > δ^C`; diverse teams are optimal iff `S < S*(δ)`; and `S*(δ)` has a
positive derivative for `δ > δ^C`. -/
theorem proposition_2 (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd)
    (hratio : fs.f0 / fs.f2 > fd.f0 / fd.f2) (ws wd : ℝ → ℝ)
    (hws : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasS c fs δ) (ws δ))
    (hwd : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasD c fd δ) (wd δ)) :
    StrictAntiOn (fun δ => expWage fs (ws δ) - expWage fd (wd δ)) (Set.Icc 0 (deltaC fs)) ∧
      StrictMonoOn (fun δ => expWage fs (ws δ) - expWage fd (wd δ)) (Set.Ioc (deltaC fs) 1) ∧
      (∀ δ ∈ Set.Icc (0 : ℝ) 1, ∀ S : ℝ, 0 < S →
        (S < Sstar fs fd (expWage fs (ws δ) - expWage fd (wd δ)) →
            Vd fd S (wd δ) > Vs fs S (ws δ)) ∧
          (Sstar fs fd (expWage fs (ws δ) - expWage fd (wd δ)) ≤ S →
            Vs fs S (ws δ) ≥ Vd fd S (wd δ))) ∧
      (∀ δ ∈ Set.Ioo (deltaC fs) 1,
        0 < deriv (fun t => Sstar fs fd (expWage fs (ws t) - expWage fd (wd t))) δ) := by sorry

end TeamDiversity.WageGap
