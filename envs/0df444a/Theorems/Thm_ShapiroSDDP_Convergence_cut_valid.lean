-- Prove2me | Theorems.Thm_ShapiroSDDP_Convergence_cut_valid
-- name    : ShapiroSDDP.Convergence.cut_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:12.057825+00:00
-- url     : https://prove2.me/theorems/7c859810-77c7-40c8-a008-98dd5f08b968
-- title:
--   §3, pp. 7–8 — the constructed planes are cutting planes: 𝔔_{t+1} ≤ 𝒬̃_{t+1} and Q̲̃_{t+1,j} ≤ Q̃_{t+1,j} along every run
-- statement:
--   Consider the SAA problem with finite-valued cost-to-go functions on reachable decisions, valid initial cut sets $C_0$, any oracle, and any run of the SDDP method (any forward samples and any choice of basic optimal dual solutions). Then for every iteration $k$ and every stage $1\le t\le T-1$:
--
--   1. every cut $(\alpha,\beta)$ of the stage-$t$ set at iteration $k$ is a cutting plane of $\widetilde{\mathcal Q}_{t+1}$ on reachable decisions:
--   $$\alpha+\beta^\top x\le\widetilde{\mathcal Q}_{t+1}(x)\qquad\text{for every reachable }x\in\mathbb R^{n_t},$$
--   so that $\mathfrak Q_{t+1}\le\widetilde{\mathcal Q}_{t+1}$ there;
--   2. for every reachable $x_t$, every outcome $j$ of stage $t+1$ and every feasible $y$ of the stage-$(t+1)$ problem, the point $(y,\widetilde{\mathcal Q}_{t+2}(y))$ is feasible for the stage-$(t+1)$ problem with the iteration-$k$ cuts. Hence the optimal value $\underline{\widetilde Q}_{t+1,j}(x_t)$ of the problem with cuts is at most $\widetilde Q_{t+1,j}(x_t)$, and $\underline{\widetilde{\mathcal Q}}_{t+1}\le\widetilde{\mathcal Q}_{t+1}$.
--
--   The paper notes that from $t=T-1$ on the constructed planes are supporting planes of $\underline{\widetilde{\mathcal Q}}_t$ but may be only cutting planes of $\widetilde{\mathcal Q}_t$. This statement is the "cutting plane" half of that remark, and it is the basis of the lower bound and of the convergence argument.
--
--   **Formalization Note** The cost-to-go values are evaluated only at reachable decisions, where they are genuine infima. Conclusion 2 avoids the infimum of the problem with cuts by exhibiting a feasible point of objective $\tilde c_{t+1,j}^\top y+\widetilde{\mathcal Q}_{t+2}(y)$. No sampling hypothesis, (A1) or oracle property is needed.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, p. 7 (before (3.8) and after (3.11)) and p. 8, §3, first paragraph

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model
import Definitions.Def_ShapiroSDDP_Convergence_SDDP

namespace ShapiroSDDP.Convergence

/-- §3, pp. 7–8: along every run of the SDDP method, every cut of every iteration is a cutting
plane of the SAA cost-to-go on reachable decisions, `α + βᵀ x ≤ 𝒬̃_{t+1}(x)`, so `𝔔_{t+1} ≤ 𝒬̃_{t+1}`;
and for every reachable `x_t`, outcome `j` and feasible `y` of the stage-`(t+1)` problem, the point
`(y, 𝒬̃_{t+2}(y))` is feasible for the stage-`(t+1)` problem with cuts, so that
`Q̲̃_{t+1,j}(x_t) ≤ Q̃_{t+1,j}(x_t)`. -/
theorem cut_valid (I : Instance) (hfin : FiniteValued I) (C₀ : (t : ℕ) → Finset (Cut I t))
    (hC₀ : ValidInit I C₀) (sol : Oracle I) {M : ℕ} (ω : ℕ → Fin M → Scen I)
    (cuts : ℕ → (t : ℕ) → Finset (Cut I t)) (hrun : IsRun I C₀ sol ω cuts) :
    (∀ k t, 1 ≤ t → t + 1 ≤ I.T → ∀ a ∈ cuts k t, ∀ x ∈ Reach I t, cutEval a x ≤ V I t x) ∧
      ∀ k t, 1 ≤ t → t + 1 ≤ I.T → ∀ x ∈ Reach I t, ∀ j : Fin (I.N (t + 1)),
        ∀ y ∈ Feas I t x j,
          (y, V I (t + 1) y) ∈ CutLPFeas (I.A t j) (rhs I t x j) (cuts k (t + 1)) := by sorry

end ShapiroSDDP.Convergence
