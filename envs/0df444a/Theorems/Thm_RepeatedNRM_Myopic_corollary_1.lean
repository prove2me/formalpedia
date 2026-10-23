-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_corollary_1
-- name    : RepeatedNRM.Myopic.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:09.378183+00:00
-- url     : https://prove2.me/theorems/d0fe0749-da40-4874-b4e3-3d9d98c66428
-- title:
--   Corollary 1, p. 23 — at γ = 0 the optimal revenue J*_T is monotone in the initial budgets
-- statement:
--   Assume every $\varphi_j$ satisfies Assumption 1 and Assumption 2 holds with $\gamma=0$. Let $\mathbf b_{1,h},\mathbf b_{1,l}\in[0,1]^m$ with $\mathbf b_{1,h}\ge\mathbf b_{1,l}$ componentwise. Then for every horizon $T\ge 2$
--   $$J^*_T(\mathbf b_{1,h})\ \ge\ J^*_T(\mathbf b_{1,l}).$$
--   Equivalently, for every feasible trajectory of (5) from $\mathbf b_{1,l}$ there is a feasible trajectory from $\mathbf b_{1,h}$ whose revenue over $T$ periods is at least as large.
--
--   In contrast with Proposition 1, where larger budgets can hurt, at $\gamma=0$ the platform always benefits from customers with higher budgets.
--
--   Differences from the source:
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - encoding: $J^*_T(\mathbf b_{1,h})\ge J^*_T(\mathbf b_{1,l})$ with $J^*_T$ the maximum of (5) → every feasible trajectory from $\mathbf b_{1,l}$ is matched in revenue by some feasible trajectory from $\mathbf b_{1,h}$; reason: equivalent because (5) is a maximum (attained; at $\gamma=0$ by the myopic policy, Theorem 2); avoids a real supremum
--   - encoding: allocations and budgets for periods $t = 1,\dots,T$ → sequences indexed by all $t\in\mathbb N$, with index $t$ standing for period $t+1$ and only indices $0,\dots,T-1$ summed; reason: a $T$-period trajectory always extends (the zero allocation is feasible and budgets stay in $[0,1]$; (7) attains its maximum), so no instance changes
--   - encoding: periods $t=1,\dots,T$ and $\varphi^{t-1}$ → `Finset.range T` with index $t$ for period $t+1$, and $\varphi^t$ with $\varphi^0 = \mathrm{id}$; reason: re-indexing only
--   - generalization: service quality (3): $q_j = U_j/U^*_j$ if $b_j>0$, $q_j = 1$ if $b_j = 0$ (undefined when $U^*_j(b_j)=0<b_j$) → $q_j = 1$ if $b_j = 0$ or $U^*_j(b_j) = 0$, else $U_j/U^*_j$; reason: (3) divides by $U^*_j(b_j)$, which is $0$ for $b_j>0$ exactly when no desired product has positive surplus or supply; Lean also covers these instances, where the paper's model is undefined, and agrees with (3) wherever (3) is defined
--   - encoding: Assumption 2(i), which divides by $p_{ij}$ for $i\in A_j$ → Assumption 2 includes $p_{ij}>0$ for $i\in A_j$; reason: the ratios $v_{ij}/p_{ij}$ are undefined otherwise; this excludes only undefined cases
--   - encoding: $\min_{i\in A_j} v_{ij}/p_{ij} - 1 \ge (1-\gamma)(\max_{i\in A_j} v_{ij}/p_{ij} - 1)$ → $v_{ij}/p_{ij} - 1 \ge (1-\gamma)(v_{kj}/p_{kj} - 1)$ for all $i,k\in A_j$; reason: equivalent for nonempty $A_j$; for empty $A_j$ the min and max are undefined and the pairwise clause is vacuous
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. 23, Corollary 1 (restated and proved p. ec7)

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

theorem corollary_1 (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n))
    (h1 : ∀ j, Assumption1i I j ∧ Assumption1ii I j ∧ Assumption1iii I j)
    (h2 : Assumption2 I A 0) (bh bl : Fin I.m → ℝ) (hbh : ∀ j, bh j ∈ Set.Icc (0 : ℝ) 1)
    (hbl : ∀ j, bl j ∈ Set.Icc (0 : ℝ) 1) (hle : ∀ j, bl j ≤ bh j) (T : ℕ) (hT : 2 ≤ T) :
    ∀ (x : ℕ → Fin I.n → Fin I.m → ℝ) (b : ℕ → Fin I.m → ℝ), IsTrajectory I bl x b →
      ∃ (x' : ℕ → Fin I.n → Fin I.m → ℝ) (b' : ℕ → Fin I.m → ℝ), IsTrajectory I bh x' b' ∧
        ∑ t ∈ Finset.range T, revenue I (x t) ≤ ∑ t ∈ Finset.range T, revenue I (x' t) := by sorry
end RepeatedNRM.Myopic
