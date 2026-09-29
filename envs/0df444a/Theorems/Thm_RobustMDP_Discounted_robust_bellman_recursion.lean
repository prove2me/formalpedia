-- Prove2me | Theorems.Thm_RobustMDP_Discounted_robust_bellman_recursion
-- name    : RobustMDP.Discounted.robust_bellman_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:01:17.781648+00:00
-- url     : https://prove2.me/theorems/83f7f179-bbc8-458c-a5c3-640962ff5aa4
-- title:
--   Theorem 3, p. 785 — Robust Bellman Recursion
-- statement:
--   Consider the discounted infinite-horizon robust control problem (6) with rectangular uncertainty: nonempty row sets $\mathcal P_i^a \subseteq \Delta_n$, costs $c(i, a) \ge 0$, discount factor $\nu \in [0, 1)$, stationary control policies $\Pi_s$ and stationary policies of nature $\mathcal T_s$. Fix the initial state $i_0$. Then there is a vector $v \in \mathbb R^n$, the value function, such that:
--
--   1. **Optimality equation (19).** $v$ is the unique solution of
--   $$v(i) = \min_{a \in \mathcal A} \big(c(i, a) + \nu\, \sigma_{\mathcal P_i^a}(v)\big), \qquad i \in \mathcal X.$$
--   2. **Value iteration (20).** For every initial vector $v_1$, the sequence $v_{k+1}(i) = \min_{a} \big(c(i, a) + \nu\, \sigma_{\mathcal P_i^a}(v_k)\big)$ converges to $v$.
--   3. **Perfect duality.**
--   $$\phi_\infty(\Pi_s, \mathcal T_s) = \min_{\pi \in \Pi_s} \sup_{\tau \in \mathcal T_s} C_\infty(\pi, \tau) = v(i_0) = \sup_{\tau \in \mathcal T_s} \min_{\pi \in \Pi_s} C_\infty(\pi, \tau) = \psi_\infty(\Pi_s, \mathcal T_s).$$
--   4. **Optimal policy (21).** Every stationary policy with $\mathbf a^*(i) \in \arg\min_a \{c(i, a) + \nu\, \sigma_{\mathcal P_i^a}(v)\}$ for all $i$ is optimal: $\sup_{\tau \in \mathcal T_s} C_\infty(\pi^*, \tau) = v(i_0)$.
--   5. **Optimal nature (22).** Every stationary policy of nature whose rows satisfy $p_i^a \in \arg\max\{p^T v : p \in \mathcal P_i^a\}$ is optimal for nature: $\min_{\pi \in \Pi_s} C_\infty(\pi, \tau^*) = v(i_0)$.
--   6. **Evaluation (23).** For every stationary policy $\pi = (\mathbf a, \mathbf a, \dots)$, the equation $v^\pi(i) = c(i, \mathbf a(i)) + \nu\, \sigma_{\mathcal P_i^{\mathbf a(i)}}(v^\pi)$ has a unique solution, and $\sup_{\tau \in \mathcal T_s} C_\infty(\pi, \tau) = v^\pi(i_0)$.
--
--   The theorem reduces the robust discounted problem to a fixed-point equation that differs from the nominal Bellman equation only by replacing an expectation with a support function, and shows that the order of play between controller and nature does not change the value.
--
--   **Formalization Note** The paper writes every maximum over nature as "max". The row sets need not be closed, so these are suprema: `IsLUB` of the set of costs, or `⨆` inside the min–max value, whose inner set is bounded above by conclusion 6. Minima over the finite set $\Pi_s$ are `⨅`. The argmax rows of (22) exist only when the maxima are attained, so conclusion 5 is stated for nature policies that attain them. The discount range is $[0, 1)$ as in the theorem. $C_\infty$ is the expected discounted sum along the Markov chain, not a fixed point.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 785, Theorem 3 (Eqs. (19)–(23)); problem (6) on p. 782

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_Discounted_discountedCost
import Definitions.Def_RobustMDP_Discounted_bellmanOps

namespace RobustMDP.Discounted

/-- Theorem 3 (Robust Bellman Recursion), Nilim–El Ghaoui 2005, p. 785.
For a discounted infinite-horizon MDP with rectangular uncertainty (nonempty row sets
`𝒫_i^a ⊆ Δ_n`, no other assumption), discount `ν ∈ [0, 1)`, stationary control policies `Π_s`,
stationary nature policies `𝒯_s`, initial state `i₀`, and `C_∞(π, P)` the discounted cost,
there is a vector `v` (the value function) such that:

1. (19) `v = g(v)` with `g` the robust Bellman operator `g(v)_i = min_a (c(i, a) + ν σ_{𝒫_i^a}(v))`,
   and `v` is the only solution of (19);
2. (20) for every initial vector `v_1`, the value-iteration sequence `v_{k+1} = g(v_k)` converges
   to `v`;
3. perfect duality with value `v(i₀)`:
   `min_{π ∈ Π_s} sup_{P ∈ 𝒯_s} C_∞(π, P) = v(i₀)` and `sup_{P ∈ 𝒯_s} min_{π ∈ Π_s} C_∞(π, P) = v(i₀)`;
4. (21) every stationary policy `π*` with `𝐚*(i) ∈ argmin_a {c(i, a) + ν σ_{𝒫_i^a}(v)}` is
   optimal: `sup_{P ∈ 𝒯_s} C_∞(π*, P) = v(i₀)`;
5. (22) every stationary nature policy `P*` whose rows attain `σ_{𝒫_i^a}(v)` is optimal for
   nature: `min_{π ∈ Π_s} C_∞(π, P*) = v(i₀)`;
6. (23) for every stationary policy `π`, the equation `v^π(i) = c(i, 𝐚(i)) + ν σ_{𝒫_i^{𝐚(i)}}(v^π)`
   has exactly one solution `v^π`, and `sup_{P ∈ 𝒯_s} C_∞(π, P) = v^π(i₀)`.

Minima over the finite set `Π_s` are `⨅`; suprema over the (generally infinite) set `𝒯_s` are
least upper bounds (`IsLUB`), or `⨆` inside the min–max value of 3, where conclusion 6 shows the
set is bounded above. The row maxima of (22) need not be attained, so 5 is stated for nature
policies that attain them. -/
theorem robust_bellman_recursion {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (i₀ : Fin n) :
    ∃ v : Fin n → ℝ,
      (M.bellmanOp v = v ∧ ∀ w, M.bellmanOp w = w → w = v) ∧
      (∀ v₁ : Fin n → ℝ,
        Filter.Tendsto (fun k : ℕ => M.bellmanOp^[k] v₁) Filter.atTop (nhds v)) ∧
      ((⨅ π : StationaryPolicy n A, ⨆ P : M.StationaryNature, M.discountedCost i₀ π P) = v i₀ ∧
        IsLUB (Set.range fun P : M.StationaryNature =>
          ⨅ π : StationaryPolicy n A, M.discountedCost i₀ π P) (v i₀)) ∧
      (∀ πstar : StationaryPolicy n A,
        (∀ (i : Fin n) (a : A),
          M.cost i (πstar i) + M.discount * Shared.supportFunction (M.rows (πstar i) i) v ≤
            M.cost i a + M.discount * Shared.supportFunction (M.rows a i) v) →
        IsLUB (Set.range fun P : M.StationaryNature => M.discountedCost i₀ πstar P) (v i₀)) ∧
      (∀ Pstar : M.StationaryNature,
        (∀ (a : A) (i : Fin n),
          ∑ j, Pstar.1 a i j * v j = Shared.supportFunction (M.rows a i) v) →
        (⨅ π : StationaryPolicy n A, M.discountedCost i₀ π Pstar) = v i₀) ∧
      (∀ π : StationaryPolicy n A,
        ∃ vπ : Fin n → ℝ,
          M.policyOp π vπ = vπ ∧ (∀ w, M.policyOp π w = w → w = vπ) ∧
          IsLUB (Set.range fun P : M.StationaryNature => M.discountedCost i₀ π P) (vπ i₀)) := by sorry

end RobustMDP.Discounted
