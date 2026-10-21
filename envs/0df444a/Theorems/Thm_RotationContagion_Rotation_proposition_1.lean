-- Prove2me | Theorems.Thm_RotationContagion_Rotation_proposition_1
-- name    : RotationContagion.Rotation.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:41.163146+00:00
-- url     : https://prove2.me/theorems/752357b0-e378-45bd-b25f-73ff5a03cdeb
-- title:
--   Proposition 1, p. 10 — frequent rotation is optimal if R/2 < b; activating one group throughout is optimal if R/2 > b
-- statement:
--   Assume $\gamma > 0$, $K > 1$, $R \ge 0$, and let $b = \frac1\gamma\ln(K-1)$ be the time the uninterrupted logistic diffusion takes to infect half a group. Let $\mu$ be any probability measure on $[0,\infty)$, the law of the infection time $t^*$; the infected group $\omega$ is uniform on $\{0,1\}$ and independent of $t^*$, and prevalence evolves by equation (2). Consider the rotation problem
--   $$\min_r\ \mathrm E\, p^\omega_{t^*+R}(\omega). \tag{P1}$$
--
--   1. If it takes more than half of the reaction time to infect half of the group, $R/2 < b$, then the frequent rotation, $r(0,t) = r(1,t) = \tfrac12$ for all $t$, is optimal.
--   2. If it takes less than half of the reaction time to infect half of the group, $R/2 > b$, then it is optimal to activate the same group at all times: for either $i = 0$ or $i = 1$, the schedule $r(i,t) = 1$ (and $r(1-i,t) = 0$) for all $t$ is optimal.
--
--   Optimal means: the schedule has a prevalence path for every infected group and infection time, and its expected terminal prevalence is no larger than that of any rotation schedule. The result says that, in this model, the choice between keeping the two groups' exposure equal and concentrating all exposure on one group is decided by comparing half the reaction time with the half-infection time.
--
--   **Formalization Note** Optimality is required for every law $\mu$ of $t^*$, as footnote 7 says the law is irrelevant. "For either $i$" is read as: both one-group schedules are optimal. The boundary case $R/2 = b$ is excluded, as on the page. When $1 < K < 2$, $b < 0$ and part 1 is vacuous, as in the paper.
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), p. 10, Proposition 1

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

namespace RotationContagion.Rotation

open MeasureTheory

/-- Proposition 1, p. 10: if `R/2 < b`, the frequent rotation `r(0, t) = r(1, t) = 1/2` solves
the rotation problem (P1); if `R/2 > b`, activating the same group at all times solves (P1), for
either group. Optimality holds for every law `μ` of the infection time on `[0, ∞)`. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) :
    (P.R / 2 < b P → IsOptimal P μ freqSched) ∧
      (b P < P.R / 2 → ∀ i : Fin 2, IsOptimal P μ (oneGroupSched i)) := by sorry

end RotationContagion.Rotation
