-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_lemma_6
-- name    : StructEstMDP.FiniteTime.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:22.360921+00:00
-- url     : https://prove2.me/theorems/37d3ca44-ad92-4677-a8e3-efe2e5155366
-- title:
--   Lemma 6, p. 19 — for a fixed policy the soft Q-function is L_r/(1−γ)-Lipschitz in the reward parameter
-- statement:
--   Let $(\mathcal S,\mathcal A,P)$ be a finite MDP with discount $\gamma\in[0,1)$, and let the reward satisfy Assumption 3 with constant $L_r$. For a policy $\pi$ and a parameter $\theta$ write $Q^\pi_\theta$ for the soft Q-function (14b) of the pair $(\theta,\pi)$. Then for every policy $\pi$, all $\theta,\theta'$ and all $(s,a)$,
--
--   $$|Q^\pi_\theta(s,a)-Q^\pi_{\theta'}(s,a)|\le L_q\|\theta-\theta'\|,\qquad L_q=\frac{L_r}{1-\gamma}.$$
--
--   With $\pi=\pi_{k+1}$, $\theta=\theta_k$ and $\theta'=\theta_{k+1}$ this is (31), $|Q_{k+\frac12}(s,a)-Q_{k+1}(s,a)|\le L_q\|\theta_k-\theta_{k+1}\|$, which bounds the effect of the reward update on the soft Q-function of the current policy.
--
--   **Formalization Note** The page states the inequality for the iterates of approximate soft policy iteration; the proof uses only that both Q-functions belong to the same policy, so the Lean states it for every policy.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 19, Lemma 6, (31); proof §19, pp. 39–40

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Lemma 6, p. 19: for a fixed policy `π`, the soft Q-function is `L_q`-Lipschitz in the reward
parameter, `|Q^π_θ(s,a) − Q^π_{θ'}(s,a)| ≤ L_q ‖θ − θ'‖` with `L_q = L_r/(1−γ)`. Applied with
`π = π_{k+1}`, `θ = θ_k`, `θ' = θ_{k+1}` this is (31). -/
theorem lemma_6 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Lr Lg : ℝ)
    (h3 : Assumption3 r Lr Lg)
    (π : S → A → ℝ) (hπ : IsPolicy π) (θ θ' : EuclideanSpace ℝ (Fin p)) (s : S) (a : A) :
    |softQ P γ r θ π s a - softQ P γ r θ' π s a| ≤ Lr / (1 - γ) * ‖θ - θ'‖ := by sorry

end StructEstMDP.FiniteTime
