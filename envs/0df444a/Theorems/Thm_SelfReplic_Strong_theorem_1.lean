-- Prove2me | Theorems.Thm_SelfReplic_Strong_theorem_1
-- name    : SelfReplic.Strong.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:54.719766+00:00
-- url     : https://prove2.me/theorems/0dcf79a9-571d-479f-8d58-ff4c877e2fcd
-- title:
--   Theorem 1, p. 10 — under Strong Replicability, the optimal policy switches sales on once (I_L < I̲), production on once (I̲ < I_L < Ī), or never produces (I_L > Ī)
-- statement:
--   Consider the base model under the standing assumptions, and assume Strong Replicability $(r-\rho)\pi>cr+h$. Let $\underline I$ be a level of the launch inventory at which always keeping production and sales on depletes the inventory exactly at $T$. Let $\overline I$ be a level at which always keeping production off and sales on depletes the inventory exactly at $T$. All other parameters are unchanged.
--
--   1. If $I_L<\underline I$, there are a time $t_s\in[0,T]$ and an optimal trajectory with production always on ($p=rI$ on $[0,T]$), sales off before $t_s$ and on from $t_s$ ($s=0$ on $[0,t_s)$, $s=d$ on $[t_s,T]$), whose inventory is depleted exactly at $T$.
--   2. If $\underline I<I_L<\overline I$, there are a time $t_p\in[0,T]$ and an optimal trajectory with sales always on ($s=d$ on $[0,T]$), production off before $t_p$ and on from $t_p$, whose inventory is depleted exactly at $T$.
--   3. If $I_L>\overline I$, there is an optimal trajectory with sales always on and production always off, and its inventory at $T$ is positive, $I(T)>0$.
--
--   "Optimal" means
--   $$\int_0^T\big[\pi s-cp-hI\big]e^{-\rho t}\,dt\;\ge\;\int_0^T\big[\pi \tilde s-c\tilde p-h\tilde I\big]e^{-\rho t}\,dt$$
--   for every admissible trajectory $(\tilde D,\tilde S,\tilde I,\tilde p,\tilde s)$ with the same parameters. Here "depleted exactly at $T$" means $I(T)=0$ and $I(t)>0$ for $0\le t<T$.
--
--   This is the paper's main result. Under Strong Replicability, replicating and selling later beats selling now. The optimal policy therefore uses all production capacity and holds back sales when the launch inventory is small. It keeps sales on and delays production when the launch inventory is moderate, and it never produces when the launch inventory alone outlasts demand.
--
--   **Formalization Note** The competitor ranges over all admissible trajectories, not over policies of the stated shape. The thresholds are taken as real numbers with their defining property. The boundary cases $I_L=\underline I$ and $I_L=\overline I$ are excluded, as on the page. The paper's remark that these policies are unique (p. 11) is not part of the theorem and is not stated.
-- source:
--   Hu & Sun, Managing self-replicating innovative goods, authors' manuscript of 2020-10-18 (Management Science, doi:10.1287/mnsc.2020.3936), p. 10, Theorem 1 (proof pp. 36–37)

import Mathlib
import Definitions.Def_SelfReplic_Strong_Model

namespace SelfReplic.Strong

/-- Theorem 1 (Strong Replicability), p. 10. With I̲ = `Ilow` and Ī = `Ihigh` the threshold
levels of the launch inventory:
(a) if `I_L < I̲`, a trajectory with production always on and sales switched on once, depleting
the inventory exactly at `T`, is optimal;
(b) if `I̲ < I_L < Ī`, a trajectory with sales always on and production switched on once,
depleting the inventory exactly at `T`, is optimal;
(c) if `I_L > Ī`, the trajectory with sales always on and production off is optimal and leaves
inventory at `T`. Optimality is against every admissible trajectory. -/
theorem theorem_1 (P : Params) (hP : P.Standing) (hSR : P.StrongRepl)
    (Ilow Ihigh : ℝ) (hlow : IsLowLevel P Ilow) (hhigh : IsHighLevel P Ihigh) :
    (P.IL < Ilow → ∃ ts ∈ Set.Icc 0 P.T, ∃ x : Traj,
        IsOptimal P x ∧ ProdAlwaysOn P x ∧ SalesOnFrom P x ts ∧ DepletedExactlyAtT P x) ∧
    (Ilow < P.IL → P.IL < Ihigh → ∃ tp ∈ Set.Icc 0 P.T, ∃ x : Traj,
        IsOptimal P x ∧ SalesAlwaysOn P x ∧ ProdOnFrom P x tp ∧ DepletedExactlyAtT P x) ∧
    (Ihigh < P.IL → ∃ x : Traj,
        IsOptimal P x ∧ SalesAlwaysOn P x ∧ ProdAlwaysOff P x ∧ 0 < x.I P.T) := by sorry

end SelfReplic.Strong
