-- Prove2me | Theorems.Thm_RobustMDP_FiniteHorizon_robust_dynamic_programming
-- name    : RobustMDP.FiniteHorizon.robust_dynamic_programming
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:22:26.567609+00:00
-- url     : https://prove2.me/theorems/cf0e4f4b-38d5-4f2f-ab46-40c2126397b0
-- title:
--   Theorem 1 (Robust Dynamic Programming) — perfect duality and the robust Bellman recursion
-- statement:
--   Consider a finite-horizon MDP with states $\mathcal X=\{1,\dots,n\}$, horizon $T=\{0,\dots,N-1\}$, a finite nonempty action set $\mathcal A$, nonnegative stage costs $c_t(i,a)$, a terminal cost $c_N$, an initial state $i_0$, and rectangular uncertainty: nonempty sets $\mathcal P_i^a\subseteq\Delta_n$ of possible $i$-th rows of the transition matrix under action $a$ (no other assumption). Let $\Pi$ be the deterministic Markov controller policies, $\mathcal T$ the admissible time-varying policies of nature, and $C_N(\pi,\tau)$ the expected total cost (2). Let $v$ be given by the robust recursion (7) and, for $\pi\in\Pi$, $v^\pi$ by recursion (10), both with terminal value $c_N$. Then:
--
--   1. **Perfect duality** holds, with value given by (7):
--
--   $$
--   \varphi_N(\Pi,\mathcal T)=\min_{\pi\in\Pi}\sup_{\tau\in\mathcal T}C_N(\pi,\tau)=v_0(i_0)=\sup_{\tau\in\mathcal T}\min_{\pi\in\Pi}C_N(\pi,\tau)=\psi_N(\Pi,\mathcal T).
--   $$
--
--   2. For every $\pi\in\Pi$, the worst-case cost is given by (10): $\sup_{\tau\in\mathcal T}C_N(\pi,\tau)=v_0^\pi(i_0)$.
--   3. Every policy $\pi^*=(\mathbf a_0^*,\dots,\mathbf a_{N-1}^*)$ with $\mathbf a_t^*(i)\in\arg\min_{a\in\mathcal A}\{c_t(i,a)+\sigma_{\mathcal P_i^a}(v_{t+1})\}$ for all $t,i$ (rule (8)) is optimal: $\sup_{\tau\in\mathcal T}C_N(\pi^*,\tau)=v_0(i_0)$.
--   4. Every policy of nature $\tau^*$ whose rows satisfy $p_i^a(t)\in\arg\max\{p^{\mathsf T}v_{t+1}:p\in\mathcal P_i^a\}$ for all $t,a,i$ (rule (9)) is a worst case: $\min_{\pi\in\Pi}C_N(\pi,\tau^*)=v_0(i_0)$, and $C_N(\pi^*,\tau^*)=v_0(i_0)$ for every $\pi^*$ as in 3.
--
--   The theorem says that the robust control problem with time-varying rectangular uncertainty is solved by a dynamic programming recursion of the same form as the nominal one, with the expected continuation cost replaced by a support function, and that the order of play between controller and nature does not matter. Convexity of the uncertainty sets is not required.
--
--   **Formalization Note** $\Pi$ is finite and nonempty, so minima over it are Lean's `⨅`. The paper writes "max" over nature; the row sets need not be closed, so these are suprema `⨆` over the nonempty set $\mathcal T$, whose costs are bounded above because every row lies in $\Delta_n$. For the same reason the maxima in (9) need not be attained, and conclusion 4 is stated for nature policies that attain them. The argmin rule (8) is stated for every policy attaining the minimum, not a particular choice. The terminal value $v_N=c_N$ is implicit in the paper's proof and explicit on p. 785. The paper's "$(\mathbf a_0,\dots,\mathbf a_N)$" in the sentence before (10) is read as $(\mathbf a_0,\dots,\mathbf a_{N-1})$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), pp. 782–783, Theorem 1

import Mathlib
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_FiniteHorizon_Model
import Definitions.Def_RobustMDP_FiniteHorizon_expectedCost
import Definitions.Def_RobustMDP_FiniteHorizon_robustValue

namespace RobustMDP.FiniteHorizon

/-- Theorem 1 (Robust Dynamic Programming), Nilim–El Ghaoui 2005, pp. 782–783.
For a finite-horizon MDP with rectangular uncertainty (nonempty row sets `𝒫_i^a ⊆ Δ_n`, no other
assumption), initial state `i₀`, and `C_N(π, τ)` the expected total cost (2):

1. perfect duality holds, with value given by recursion (7):
   `min_{π ∈ Π} sup_{τ ∈ 𝒯} C_N(π, τ) = v_0(i₀) = sup_{τ ∈ 𝒯} min_{π ∈ Π} C_N(π, τ)`;
2. for every policy `π`, the worst case `sup_{τ ∈ 𝒯} C_N(π, τ)` is `v_0^π(i₀)`, recursion (10);
3. every policy `π*` whose actions attain the minimum in (8),
   `𝐚*_t(i) ∈ argmin_a {c_t(i, a) + σ_{𝒫_i^a}(v_{t+1})}`, is optimal:
   `sup_{τ ∈ 𝒯} C_N(π*, τ) = v_0(i₀)`;
4. every nature policy `τ*` whose rows attain the maxima in (9),
   `p_i^a(t) ∈ argmax {pᵀ v_{t+1} : p ∈ 𝒫_i^a}`, is a worst case:
   `min_{π ∈ Π} C_N(π, τ*) = v_0(i₀)`, and `C_N(π*, τ*) = v_0(i₀)` for every `π*` as in 3.

`Π` is finite, so its minima are `⨅`; nature's maxima are `⨆` over the (possibly infinite) set
`𝒯`, which is nonempty and whose costs are bounded above. The row maxima of (9) need not be
attained, so conclusion 4 is stated for nature policies that attain them. -/
theorem robust_dynamic_programming {n N : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n N A) (i₀ : Fin n) :
    ((⨅ π : ControlPolicy n N A, ⨆ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1) =
        M.robustValue 0 i₀ ∧
      (⨆ τ : M.NaturePolicy, ⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τ.1) =
        M.robustValue 0 i₀) ∧
    (∀ π : ControlPolicy n N A,
      (⨆ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1) = M.policyValue π 0 i₀) ∧
    (∀ πstar : ControlPolicy n N A,
      (∀ (t : Fin N) (i : Fin n) (a : A),
        M.cost t i (πstar t i) + Shared.supportFunction (M.rows (πstar t i) i) (M.robustValue (t + 1)) ≤
          M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1))) →
      (⨆ τ : M.NaturePolicy, M.expectedCost i₀ πstar τ.1) = M.robustValue 0 i₀) ∧
    (∀ τstar : M.NaturePolicy,
      (∀ (t : Fin N) (a : A) (i : Fin n),
        ∑ j, τstar.1 t a i j * M.robustValue (t + 1) j =
          Shared.supportFunction (M.rows a i) (M.robustValue (t + 1))) →
      (⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τstar.1) = M.robustValue 0 i₀ ∧
      ∀ πstar : ControlPolicy n N A,
        (∀ (t : Fin N) (i : Fin n) (a : A),
          M.cost t i (πstar t i) + Shared.supportFunction (M.rows (πstar t i) i) (M.robustValue (t + 1)) ≤
            M.cost t i a + Shared.supportFunction (M.rows a i) (M.robustValue (t + 1))) →
        M.expectedCost i₀ πstar τstar.1 = M.robustValue 0 i₀) := by sorry

end RobustMDP.FiniteHorizon
