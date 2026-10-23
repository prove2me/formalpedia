-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_theorem_1
-- name    : RepeatedNRM.Myopic.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:07.404612+00:00
-- url     : https://prove2.me/theorems/9d023d0e-cdf2-43ab-96b2-07602f97741e
-- title:
--   Theorem 1, p. 19 — the myopic policy is (1 − γ)-optimal for the repeated network revenue management problem
-- statement:
--   Consider the repeated network revenue management problem (5): over $T$ periods the platform allocates products to $m$ customers subject to the budget constraints (1) and supply constraints (2), earning $R(x_t)=\sum_{i,j}p_{ij}x_{ij,t}$. Each customer's budget evolves through $\mathbf b_{t+1}=\boldsymbol\varphi(\mathbf b_t,\mathbf q(\mathbf b_t,x_t))$, where $q_j$ is the service quality (3) and $\varphi_j:[0,1]^2\to[0,1]$ is the budget update. The myopic policy solves in each period the linear program (7), the revenue-maximizing allocation at the current budgets, and earns $J^{MY}_T(\mathbf b_1)=\sum_{t=1}^T R(x^{MY}_t)$.
--
--   Assume every $\varphi_j$ satisfies Assumption 1 (monotonicity, $\varphi_j(b,q)\ge\min\{b,q\}$, and $\varphi^t_j(b,1-\vartheta)\ge(1-\vartheta)\varphi^t_j(b,1)$). Assume Assumption 2 holds with parameter $\gamma\in[0,1]$, i.e. each customer's bang-per-buck ratios $v_{ij}/p_{ij}-1$ over its desired products differ by at most the factor $1-\gamma$. Then for every horizon $T$ and initial budgets $\mathbf b_1\in[0,1]^m$, every trajectory of the myopic policy satisfies
--   $$J^{MY}_T(\mathbf b_1)\ \ge\ (1-\gamma)\cdot J^*_T(\mathbf b_1),$$
--   where $J^*_T(\mathbf b_1)$ is the optimal value of (5).
--
--   The guarantee does not depend on $T$, $m$ or $n$: the myopic policy does not compound its one-period loss over time. Proposition 3 shows the factor $1-\gamma$ is tight. The paper's printed proof passes through Proposition 7 ($J^{MY}_T\ge J^{LBMY}_T$), which is false; the theorem itself is posed as printed.
--
--   Differences from the source:
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - reading: "the myopic policy" $\{\mathbf x^{MY}_t\}$ → every trajectory whose allocation in each period is an optimal solution of (7) at the current budgets; reason: (7) can have several optimal solutions; the statement is made for every selection, the stronger of the two readings
--   - encoding: $J^*_T(\mathbf b_1)$, the maximum of problem (5) → an inequality against the revenue of every feasible trajectory of (5); reason: equivalent, since the maximum is the least upper bound of these revenues; avoids a real supremum
--   - encoding: allocations and budgets for periods $t = 1,\dots,T$ → sequences indexed by all $t\in\mathbb N$, with index $t$ standing for period $t+1$ and only indices $0,\dots,T-1$ summed; reason: a $T$-period trajectory always extends (the zero allocation is feasible and budgets stay in $[0,1]$; (7) attains its maximum), so no instance changes
--   - encoding: periods $t=1,\dots,T$ and $\varphi^{t-1}$ → `Finset.range T` with index $t$ for period $t+1$, and $\varphi^t$ with $\varphi^0 = \mathrm{id}$; reason: re-indexing only
--   - generalization: service quality (3): $q_j = U_j/U^*_j$ if $b_j>0$, $q_j = 1$ if $b_j = 0$ (undefined when $U^*_j(b_j)=0<b_j$) → $q_j = 1$ if $b_j = 0$ or $U^*_j(b_j) = 0$, else $U_j/U^*_j$; reason: (3) divides by $U^*_j(b_j)$, which is $0$ for $b_j>0$ exactly when no desired product has positive surplus or supply; Lean also covers these instances, where the paper's model is undefined, and agrees with (3) wherever (3) is defined
--   - encoding: Assumption 2(i), which divides by $p_{ij}$ for $i\in A_j$ → Assumption 2 includes $p_{ij}>0$ for $i\in A_j$; reason: the ratios $v_{ij}/p_{ij}$ are undefined otherwise; this excludes only undefined cases
--   - encoding: $\min_{i\in A_j} v_{ij}/p_{ij} - 1 \ge (1-\gamma)(\max_{i\in A_j} v_{ij}/p_{ij} - 1)$ → $v_{ij}/p_{ij} - 1 \ge (1-\gamma)(v_{kj}/p_{kj} - 1)$ for all $i,k\in A_j$; reason: equivalent for nonempty $A_j$; for empty $A_j$ the min and max are undefined and the pairwise clause is vacuous
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. 19, Theorem 1 (restated p. ec10)

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

theorem theorem_1 (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ)
    (h1 : ∀ j, Assumption1i I j ∧ Assumption1ii I j ∧ Assumption1iii I j)
    (h2 : Assumption2 I A γ) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1) (T : ℕ)
    (xMY : ℕ → Fin I.n → Fin I.m → ℝ) (bMY : ℕ → Fin I.m → ℝ)
    (hMY : IsMyopicTrajectory I b1 xMY bMY)
    (x : ℕ → Fin I.n → Fin I.m → ℝ) (b : ℕ → Fin I.m → ℝ) (hx : IsTrajectory I b1 x b) :
    (1 - γ) * ∑ t ∈ Finset.range T, revenue I (x t) ≤ ∑ t ∈ Finset.range T, revenue I (xMY t) := by sorry
end RepeatedNRM.Myopic
