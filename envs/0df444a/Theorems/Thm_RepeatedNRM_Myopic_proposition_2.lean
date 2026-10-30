-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_proposition_2
-- name    : RepeatedNRM.Myopic.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:01.357805+00:00
-- url     : https://prove2.me/theorems/ae656ff9-c5ed-4f57-bbeb-b662c2d7969e
-- title:
--   Proposition 2, p. 18 — the relaxation (9) bounds the optimal revenue of (5)
-- statement:
--   Consider the repeated network revenue management problem (5) with initial budgets $\mathbf b_1\in[0,1]^m$, and let $J^{\mathrm{relax}}_T(\mathbf b_1)=\sum_{t=1}^T\mathrm{MY}(\boldsymbol\varphi^{t-1}(\mathbf b_1,1))$ be the value of the relaxation (9), in which every customer's budget grows as if service quality were always $1$.
--
--   If every budget update function $\varphi_j$ satisfies Assumption 1(i) (monotone in budget and in quality on $[0,1]^2$), then for every horizon $T\ge 1$
--   $$J^{\mathrm{relax}}_T(\mathbf b_1)\ \ge\ J^*_T(\mathbf b_1).$$
--
--   Equivalently: every feasible trajectory $(x_t,\mathbf b_t)$ of (5) earns $\sum_{t=1}^T R(x_t)\le J^{\mathrm{relax}}_T(\mathbf b_1)$. The relaxation is the benchmark of Theorems 1 and 2.
--
--   Differences from the source:
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - encoding: $J^*_T(\mathbf b_1)$, the maximum of problem (5) → an inequality against the revenue of every feasible trajectory of (5); reason: equivalent, since the maximum is the least upper bound of these revenues; avoids a real supremum
--   - encoding: allocations and budgets for periods $t = 1,\dots,T$ → sequences indexed by all $t\in\mathbb N$, with index $t$ standing for period $t+1$ and only indices $0,\dots,T-1$ summed; reason: a $T$-period trajectory always extends (the zero allocation is feasible and budgets stay in $[0,1]$; (7) attains its maximum), so no instance changes
--   - encoding: periods $t=1,\dots,T$ and $\varphi^{t-1}$ → `Finset.range T` with index $t$ for period $t+1$, and $\varphi^t$ with $\varphi^0 = \mathrm{id}$; reason: re-indexing only
--   - generalization: service quality (3): $q_j = U_j/U^*_j$ if $b_j>0$, $q_j = 1$ if $b_j = 0$ (undefined when $U^*_j(b_j)=0<b_j$) → $q_j = 1$ if $b_j = 0$ or $U^*_j(b_j) = 0$, else $U_j/U^*_j$; reason: (3) divides by $U^*_j(b_j)$, which is $0$ for $b_j>0$ exactly when no desired product has positive surplus or supply; Lean also covers these instances, where the paper's model is undefined, and agrees with (3) wherever (3) is defined
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. 18, Proposition 2 (restated p. ec2)

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

theorem proposition_2 (I : Instance) (hI : I.Standing) (h1 : ∀ j, Assumption1i I j)
    (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (hT : 1 ≤ T)
    (x : ℕ → Fin I.n → Fin I.m → ℝ) (b : ℕ → Fin I.m → ℝ) (hx : IsTrajectory I b1 x b) :
    ∑ t ∈ Finset.range T, revenue I (x t) ≤ Jrelax I T b1 := by sorry
end RepeatedNRM.Myopic
