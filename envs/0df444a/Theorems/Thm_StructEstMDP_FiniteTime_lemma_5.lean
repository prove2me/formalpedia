-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_lemma_5
-- name    : StructEstMDP.FiniteTime.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:13.459226+00:00
-- url     : https://prove2.me/theorems/af90e578-4ac8-4424-8747-9e6c20887a57
-- title:
--   Lemma 5, p. 19 — the visitation measure of a softmax policy is Lipschitz: ‖d_w − d_{w′}‖_TV ≤ C_d‖w − w′‖
-- statement:
--   Let $(\mathcal S,\mathcal A,P,\rho,\gamma)$ be a finite MDP with initial distribution $\rho$ and discount $\gamma\in[0,1)$ satisfying Assumption 2. For $w\in\mathbb R^{|\mathcal S|\times|\mathcal A|}$ let $d_w(s,a)=(1-\gamma)\pi_w(a\mid s)\sum_{t\ge0}\gamma^tP^{\pi_w}(s_t=s\mid s_0\sim\rho)$ be the state-action visitation distribution of the softmax policy $\pi_w(a\mid s)=e^{w(s,a)}/\sum_b e^{w(s,b)}$. Then there is a constant $C_d>0$ such that for all $w,w'$
--
--   $$\|d_w-d_{w'}\|_{TV}\le C_d\,\|w-w'\|,$$
--
--   where $\|\cdot\|_{TV}$ is half the $\ell_1$ distance and $\|w-w'\|$ is the Euclidean norm on $\mathbb R^{|\mathcal S|\times|\mathcal A|}$.
--
--   The constant $C_d$ enters the smoothness constant $L_c$ of Lemma 3 and the bias bound (48), and through them the rate of Theorem 1.
--
--   **Formalization Note** The paper cites this result from [50, Lemma 3] and does not fix the total-variation convention; the factor $\tfrac12$ is the one the proof of (48)(ii) needs. The norm $\|w-w'\|$ is the Frobenius norm `frobNorm`, not Lean's sup norm on function types: the factor $\sqrt{|\mathcal S||\mathcal A|}$ in (48)(iv) comes from comparing the two.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 19, Lemma 5, (30) (citing [50, Lemma 3])

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Lemma 5 ([50, Lemma 3]), p. 19: the state-action visitation measure of a softmax policy is
Lipschitz in the softmax parameter, `‖d_w − d_{w'}‖_TV ≤ C_d ‖w − w'‖`, with the Euclidean
(Frobenius) norm on `ℝ^{|S|×|A|}`. -/
theorem lemma_5 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (ρ : S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hρ : IsDist ρ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h2 : Assumption2 P) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ w w' : S → A → ℝ,
      tvDist (visitation P γ ρ (softmax w)) (visitation P γ ρ (softmax w')) ≤
        Cd * frobNorm (w - w') := by sorry

end StructEstMDP.FiniteTime
