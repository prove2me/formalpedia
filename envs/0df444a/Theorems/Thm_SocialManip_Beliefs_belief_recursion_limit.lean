-- Prove2me | Theorems.Thm_SocialManip_Beliefs_belief_recursion_limit
-- name    : SocialManip.Beliefs.belief_recursion_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:18.432238+00:00
-- url     : https://prove2.me/theorems/3ab4e404-938f-4418-bf7f-4c033ba00b0b
-- title:
--   Proof of Theorem 2 (Appendix E.2), p. 47 — under Assumption 1, π_{t+1} = u_{t+1} + Wπ_t with u_t → u_∞ converges to (I − W)^{-1}u_∞
-- statement:
--   In the setting of Lemma 3 — agents split into Bayesians $B$ and DeGroot agents, nonnegative DeGroot weights with $\theta_i+\sum_j\alpha_{ij}=1$, signal qualities $p_i\in[1/2,1)$, and Assumption 1 (ii)–(iv) — let $\mathbf W$ be the influence matrix. Let $(\mathbf u_t)_{t\ge0}$ be a sequence of vectors in $\mathbb R^n$ converging to $\mathbf u_\infty$, and let $(\boldsymbol\pi_t)_{t\ge0}$ satisfy the recursion
--   $$\boldsymbol\pi_{t+1}=\mathbf u_{t+1}+\mathbf W\boldsymbol\pi_t\qquad(t\ge0).$$
--   Then $\boldsymbol\pi_t$ converges to a limit $\boldsymbol\pi_\infty$ which solves the fixed-point problem and is given explicitly:
--   $$\boldsymbol\pi_\infty=\mathbf u_\infty+\mathbf W\boldsymbol\pi_\infty,\qquad \boldsymbol\pi_\infty=(\mathbf I-\mathbf W)^{-1}\mathbf u_\infty .$$
--
--   In the proof of Theorem 2, $\mathbf u_t$ is $\boldsymbol\theta\odot\mathrm{BU}(\mathbf h_t)$ (with the correct belief in the Bayesian entries) along one realization of the signals, so this deterministic statement turns the almost-sure convergence of the personal experiences into the almost-sure convergence of the beliefs.
--
--   **Formalization Note** The statement is pathwise and deterministic: $\mathbf u$ is an arbitrary convergent sequence. The input at step $t+1$ is $\mathbf u_{t+1}$, following the DeGroot update of p. 7; the page's proof writes $\mathrm{BU}(\mathbf h_t)$, which has the same limit. The hypotheses are those of Lemma 3, which the page invokes.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), proof of Theorem 2 (Appendix E.2), p. 47, from "which implies that π^D_t must converge almost surely to some π^D_∞" to "π_∞ = (I − W)^{-1}(θ ⊙ BU(h_∞))"

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting

open Filter Topology Matrix

namespace SocialManip.Beliefs

theorem belief_recursion_limit {n : ℕ} (B : Finset (Fin n)) (θ : Fin n → ℝ) (α : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, 1 / 2 ≤ p i ∧ p i < 1)
    (hθ : ∀ i ∉ B, 0 ≤ θ i) (hα : ∀ i ∉ B, ∀ j, 0 ≤ α i j)
    (hrow : ∀ i ∉ B, θ i + ∑ j, α i j = 1)
    (adj : Fin n → Fin n → Prop) (hadj : ∀ i ∉ B, ∀ j, adj i j ↔ 0 < α i j)
    (hA1ii : ∀ i j, i ≠ j → Relation.TransGen adj i j)
    (hA1iii : ∀ i ∉ B, (0 < θ i ↔ 1 / 2 < p i))
    (hA1iv : ∃ i, 1 / 2 < p i)
    (u : ℕ → Fin n → ℝ) (uInf : Fin n → ℝ) (hu : Tendsto u atTop (𝓝 uInf))
    (π : ℕ → Fin n → ℝ) (hπ : ∀ t, π (t + 1) = u (t + 1) + W B α *ᵥ π t) :
    ∃ πInf : Fin n → ℝ, Tendsto π atTop (𝓝 πInf) ∧ πInf = uInf + W B α *ᵥ πInf ∧
      πInf = (1 - W B α)⁻¹ *ᵥ uInf := by sorry

end SocialManip.Beliefs
