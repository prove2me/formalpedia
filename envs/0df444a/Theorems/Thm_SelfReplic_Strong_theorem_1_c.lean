-- Prove2me | Theorems.Thm_SelfReplic_Strong_theorem_1_c
-- name    : SelfReplic.Strong.theorem_1_c
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T03:25:12.486237+00:00
-- url     : https://prove2.me/theorems/5643c91a-1bb7-4d5f-8b25-ce2de5a3dbc1
-- title:
--   Theorem 1(c), p. 10 — under Strong Replicability, if I_L > Ī the optimal policy keeps sales on and never produces, leaving inventory at T
-- statement:
--   Consider the base model of Hu and Sun under the standing assumptions, and assume Strong Replicability
--   $$(r-\rho)\pi>cr+h.$$
--   Let $\underline I$ be a level of the launch inventory at which always keeping production and sales on ($p=rI$, $s=d$) depletes the inventory exactly at $T$. Let $\overline I$ be a level at which always keeping production off and sales on ($p=0$, $s=d$) depletes the inventory exactly at $T$. All other parameters are unchanged.
--
--   **Case (c).** If $I_L>\overline I$, there is an optimal trajectory with sales always on ($s=d$) and production always off ($p=0$) on $[0,T]$, and its inventory at $T$ is positive, $I(T)>0$.
--
--   Here "optimal" means
--   $$\int_0^T\big[\pi s-cp-hI\big]e^{-\rho t}\,dt\;\ge\;\int_0^T\big[\pi \tilde s-c\tilde p-h\tilde I\big]e^{-\rho t}\,dt$$
--   for every admissible trajectory $(\tilde D,\tilde S,\tilde I,\tilde p,\tilde s)$ with the same parameters. "Depleted exactly at $T$" means $I(T)=0$ and $I(t)>0$ for $0\le t<T$.
--
--   This is one of the three cases of the paper's main result, Theorem 1. The three cases together are the goal theorem `SelfReplic.Strong.theorem_1`.
--
--   **Formalization Note** The binders are exactly those of `SelfReplic.Strong.theorem_1`, and the conclusion is its corresponding conjunct. The competitor ranges over all admissible trajectories, not only over policies of the stated shape. The thresholds are real numbers given with their defining property.
-- source:
--   Hu & Sun, Managing self-replicating innovative goods, authors' manuscript of 2020-10-18 (Management Science, doi:10.1287/mnsc.2020.3936), p. 10, Theorem 1(c) (proof pp. 36–37)

import Mathlib
import Definitions.Def_SelfReplic_Strong_Model

namespace SelfReplic.Strong

/-- Theorem 1(c) (Strong Replicability), p. 10: if `I_L > Ī`, the trajectory with sales always on and
production off is optimal and leaves inventory at `T`. -/
theorem theorem_1_c (P : Params) (hP : P.Standing) (hSR : P.StrongRepl)
    (Ilow Ihigh : ℝ) (hlow : IsLowLevel P Ilow) (hhigh : IsHighLevel P Ihigh) :
    Ihigh < P.IL → ∃ x : Traj,
        IsOptimal P x ∧ SalesAlwaysOn P x ∧ ProdAlwaysOff P x ∧ 0 < x.I P.T := by sorry

end SelfReplic.Strong
