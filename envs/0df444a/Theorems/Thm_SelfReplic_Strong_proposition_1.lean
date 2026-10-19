-- Prove2me | Theorems.Thm_SelfReplic_Strong_proposition_1
-- name    : SelfReplic.Strong.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:55.428572+00:00
-- url     : https://prove2.me/theorems/f57f1da4-e145-4dc6-9987-6eb11ac50b58
-- title:
--   Proposition 1, p. 9 — once production is switched on, an optimal policy keeps it on until T or inventory depletion
-- statement:
--   Consider the base model under the standing assumptions, and assume moreover $\rho c+h>0$. Let $(D,S,I,p,s)$ be an optimal trajectory, and let $0\le t_0\le t_1\le T$. Suppose production has been switched on by time $t_0$, in the sense that
--   $$\int_0^{t_0}p(u)\,du>0,$$
--   and suppose the inventory is not yet depleted at $t_1$, that is $I(t_1)>0$. Then production stays on throughout:
--   $$p(t)=rI(t)\quad\text{for almost every }t\in[t_0,t_1].$$
--
--   This is the paper's Proposition 1: after production is switched on, it is never optimal to switch it off, until $T$ or inventory depletion. It reduces the possible optimal production policies to "off on an initial interval, then on", which is the shape Theorem 1 uses.
--
--   **Formalization Note** "Switched on" and "switched off" are read up to null sets: production has run before $t_0$, and the conclusion holds almost everywhere. "Until inventory depletion" is the hypothesis $I(t_1)>0$; inventory cannot recover from $0$ because $p\le rI$. The hypothesis $\rho c+h>0$ is not on the page, where Proposition 1 is stated with no condition. It is added because without it the statement fails: when $\rho=h=0$, inventory is free to hold and production is not discounted, so production can be paused and resumed at no cost, and several optimal trajectories exist, some of which switch production off. The paper's proof (p. 35) needs $\lambda_I'>0$ at the level $\lambda_I=c$, which is $\rho c+h>0$.
-- source:
--   Hu & Sun, Managing self-replicating innovative goods, authors' manuscript of 2020-10-18 (Management Science, doi:10.1287/mnsc.2020.3936), p. 9, Proposition 1 (proof p. 35)

import Mathlib
import Definitions.Def_SelfReplic_Strong_Model

namespace SelfReplic.Strong

open MeasureTheory

/-- Proposition 1, p. 9: after production is switched on, it is never optimal to switch it off
(until `T` or inventory depletion). If an optimal trajectory has produced a positive amount by
time `t₀` and still holds inventory at `t₁ ≥ t₀`, then `p = rI` almost everywhere on `[t₀, t₁]`.
The hypothesis `0 < ρc + h` is an addition (see the natural-language statement). -/
theorem proposition_1 (P : Params) (hP : P.Standing) (hcost : 0 < P.rho * P.c + P.h)
    (x : Traj) (hx : IsOptimal P x) (t₀ t₁ : ℝ) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ P.T)
    (hon : 0 < ∫ u in (0:ℝ)..t₀, x.p u) (hI : 0 < x.I t₁) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc t₀ t₁)), x.p t = P.r * x.I t := by sorry

end SelfReplic.Strong
