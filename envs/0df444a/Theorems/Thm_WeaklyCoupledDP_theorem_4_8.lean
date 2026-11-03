-- Prove2me | Theorems.Thm_WeaklyCoupledDP_theorem_4_8
-- name    : WeaklyCoupledDP.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:44.98933+00:00
-- url     : https://prove2.me/theorems/62f167d8-245a-4af4-ba88-9524b0bfbb80
-- title:
--   Theorem 4.8 — under Assumption 4.7 the relaxation gap is zero, $V^{\lambda*}_1(s_1,e_1) = V^{\mathrm{LP}}_1(s_1,e_1)$
-- statement:
--   Consider any weakly coupled stochastic dynamic program (any horizon $T$, any number $N$ of subproblems, finite time-indexed state spaces, a finite exogenous state space with time-dependent transition kernels, state-dependent finite action sets, real rewards, arbitrary transition probabilities, and $L_t$ linking constraints with feasible sets $\mathcal A_t(s_t,e_t)$ nonempty in every state). If Assumption 4.7 holds, then the approximate linear program (5) and the Lagrangian dual problem have the same optimal value, and both optima are attained:
--   $$
--   V^{\lambda*}_1(s_1,e_1) = \min_{\lambda \in \Lambda} V^\lambda_1(s_1,e_1) \;=\; V^{\mathrm{LP}}_1(s_1,e_1) = \min\Big\{ \sum_{i=1}^N V_{1,i}(s_{1,i},e_1) : V \text{ feasible in (5)} \Big\}.
--   $$
--   So the relaxation gap is zero: when the linking constraints do not depend on the subproblem states and have a totally unimodular structure with integral right-hand sides, the Lagrangian relaxation, which decomposes across subproblems and is cheap to compute, gives the same upper bound as the approximate linear program, which in general is tighter. Restless bandits with multiple actions, online stochastic matching, network revenue management and resource relocation problems satisfy these conditions (Corollaries 4.10–4.13).
--
--   Differences from the source:
--   - generalization: V^λ*₁(s₁,e₁) = V^LP₁(s₁,e₁), two optimal values → one real number that is the least ALP objective value and the least Lagrangian value; reason: it also states that both minima are attained, which is true (an LP bounded below attains its minimum); equality of the values is the printed statement.
--   - reading: (5b) uses V_{T+1,i} without a value → ALP feasibility includes V_{T+1,i} = 0; reason: the convention V_{T+1} = 0 of (2) and (7); without it the ALP is unbounded below.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), Theorem 4.8, p.16 (PDF p.17); proof, pp.31–32 (PDF pp.32–33)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model_ALPFeasible
import Definitions.Def_WeaklyCoupledDP_Model_lagrangianValue
import Definitions.Def_WeaklyCoupledDP_Model_Assumption47

namespace WeaklyCoupledDP

/-- **Theorem 4.8** (Brown & Zhang, SSRN 3849573 (Feb. 6, 2022), p.16). If Assumption 4.7 holds, the
relaxation gap is zero, i.e., `V^λ*₁(s₁, e₁) = V^LP₁(s₁, e₁)`.

**Formalization Note.** `V^LP₁(s₁, e₁)` is the minimum of the ALP (5) and `V^λ*₁(s₁, e₁)` is
`min_{λ∈Λ} V^λ₁(s₁, e₁)`, p.9. Both are stated as `IsLeast`, so the statement also says that both
minima are attained; a real infimum would give junk values on an empty or unbounded set. -/
theorem theorem_4_8 {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*}
    {L : ℕ → ℕ} [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)
    (h : M.Assumption47) :
    ∃ v : ℝ, IsLeast {x | ∃ V : M.ValueArray, M.ALPFeasible V ∧ M.alpObjective V = x} v ∧
      IsLeast {x | ∃ lam ∈ M.Lambda, M.lagrangianValue lam 1 M.s₁ M.e₁ = x} v := by sorry

end WeaklyCoupledDP
