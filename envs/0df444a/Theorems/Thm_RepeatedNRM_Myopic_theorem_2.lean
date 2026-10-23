-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_theorem_2
-- name    : RepeatedNRM.Myopic.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:01.986787+00:00
-- url     : https://prove2.me/theorems/9f8e8065-1f58-41ee-9250-f84d25a6d67c
-- title:
--   Theorem 2, p. 22 — at γ = 0 the myopic policy is optimal for the relaxation (9) and for problem (5)
-- statement:
--   Assume every budget update function $\varphi_j$ satisfies Assumption 1(i)–(ii) and Assumption 2 holds with $\gamma=0$. Let $\mathbf b_1\in[0,1]^m$ and let $\{x^{MY}_t\}$ be a trajectory of the myopic policy: in each period $x^{MY}_t$ solves (7) at the current budgets, which then update by $\mathbf b_{t+1}=\boldsymbol\varphi(\mathbf b_t,\mathbf q(\mathbf b_t,x^{MY}_t))$. Then for every horizon $T$:
--
--   1. $\{x^{MY}_t\}$ is optimal for the relaxation (9): $$J^{MY}_T(\mathbf b_1)=J^{\mathrm{relax}}_T(\mathbf b_1).$$
--   2. $\{x^{MY}_t\}$ is optimal for problem (5): $$J^{MY}_T(\mathbf b_1)=J^*_T(\mathbf b_1),$$ i.e. no feasible trajectory of (5) earns more.
--
--   When every customer has a single bang-per-buck ratio, solving the one-period LP each period is optimal for the dynamic problem.
--
--   Differences from the source:
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - reading: "the myopic policy" $\{\mathbf x^{MY}_t\}$ → every trajectory whose allocation in each period is an optimal solution of (7) at the current budgets; reason: (7) can have several optimal solutions; the statement is made for every selection, the stronger of the two readings
--   - generalization: "under Assumptions 1 and 2 with $\gamma=0$" → Assumption 1(i) and (ii) only; Assumption 1(iii) is not a hypothesis; reason: p. 23 states that the proof does not require Assumption 1(iii); the Lean statement specialises to the printed one
--   - encoding: $J^*_T(\mathbf b_1)$, the maximum of problem (5) → an inequality against the revenue of every feasible trajectory of (5); reason: equivalent, since the maximum is the least upper bound of these revenues; avoids a real supremum
--   - encoding: allocations and budgets for periods $t = 1,\dots,T$ → sequences indexed by all $t\in\mathbb N$, with index $t$ standing for period $t+1$ and only indices $0,\dots,T-1$ summed; reason: a $T$-period trajectory always extends (the zero allocation is feasible and budgets stay in $[0,1]$; (7) attains its maximum), so no instance changes
--   - encoding: periods $t=1,\dots,T$ and $\varphi^{t-1}$ → `Finset.range T` with index $t$ for period $t+1$, and $\varphi^t$ with $\varphi^0 = \mathrm{id}$; reason: re-indexing only
--   - encoding: "for any horizon $T$" → every $T\in\mathbb N$, including $T=0$; reason: at $T=0$ every quantity is an empty sum
--   - generalization: service quality (3): $q_j = U_j/U^*_j$ if $b_j>0$, $q_j = 1$ if $b_j = 0$ (undefined when $U^*_j(b_j)=0<b_j$) → $q_j = 1$ if $b_j = 0$ or $U^*_j(b_j) = 0$, else $U_j/U^*_j$; reason: (3) divides by $U^*_j(b_j)$, which is $0$ for $b_j>0$ exactly when no desired product has positive surplus or supply; Lean also covers these instances, where the paper's model is undefined, and agrees with (3) wherever (3) is defined
--   - encoding: Assumption 2(i), which divides by $p_{ij}$ for $i\in A_j$ → Assumption 2 includes $p_{ij}>0$ for $i\in A_j$; reason: the ratios $v_{ij}/p_{ij}$ are undefined otherwise; this excludes only undefined cases
--   - encoding: $\min_{i\in A_j} v_{ij}/p_{ij} - 1 \ge (1-\gamma)(\max_{i\in A_j} v_{ij}/p_{ij} - 1)$ → $v_{ij}/p_{ij} - 1 \ge (1-\gamma)(v_{kj}/p_{kj} - 1)$ for all $i,k\in A_j$; reason: equivalent for nonempty $A_j$; for empty $A_j$ the min and max are undefined and the pairwise clause is vacuous
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. 22, Theorem 2 (proof pp. 22–23)

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

theorem theorem_2 (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n))
    (h1 : ∀ j, Assumption1i I j ∧ Assumption1ii I j)
    (h2 : Assumption2 I A 0) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1) (T : ℕ)
    (xMY : ℕ → Fin I.n → Fin I.m → ℝ) (bMY : ℕ → Fin I.m → ℝ)
    (hMY : IsMyopicTrajectory I b1 xMY bMY) :
    ∑ t ∈ Finset.range T, revenue I (xMY t) = Jrelax I T b1 ∧
      ∀ (x : ℕ → Fin I.n → Fin I.m → ℝ) (b : ℕ → Fin I.m → ℝ), IsTrajectory I b1 x b →
        ∑ t ∈ Finset.range T, revenue I (x t) ≤ ∑ t ∈ Finset.range T, revenue I (xMY t) := by sorry
end RepeatedNRM.Myopic
