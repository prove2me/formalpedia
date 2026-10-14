-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_display_after_44
-- name    : StructEstMDP.FiniteTime.display_after_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:16.006145+00:00
-- url     : https://prove2.me/theorems/2cefa8a9-f8f4-487d-8b3c-b6bebd2eac38
-- title:
--   Display after (44), p. 22 — averaged tracking error (1/K)Σ‖Q_k − Q_{θ_k}‖_∞ ≤ C₀/(K(1−γ)) + 2γε/(1−γ)² + 4L_q²α/(1−γ)
-- statement:
--   Let $(\mathcal S,\mathcal A,P)$ be a finite MDP with discount $\gamma\in[0,1)$, let the reward satisfy Assumption 3 with constant $L_r$, and write $L_q=L_r/(1-\gamma)$. Consider any run of Algorithm 1 with step size $\alpha\ge0$, policy-evaluation error $\varepsilon$, initial parameter $\theta_0$ and initial policy $\pi_0$; let $Q_k$ be the soft Q-function of $(\theta_k,\pi_k)$ and $C_0=\|Q_0-Q_{\theta_0}\|_\infty$. Then for every $K\ge1$ and every realization of the run,
--
--   $$\frac1K\sum_{k=0}^{K-1}\|Q_k-Q_{\theta_k}\|_\infty\le\frac{C_0}{K(1-\gamma)}+\frac{2\gamma\varepsilon}{(1-\gamma)^2}+\frac{4L_q^2}{1-\gamma}\alpha.$$
--
--   With $\alpha=\alpha_0/K^\sigma$ the right side is $O(K^{-1})+O(K^{-\sigma})+O(\varepsilon)$, which is (45); it is the lower-level convergence on which both parts of Theorem 1 rest.
--
--   **Formalization Note** The bound holds pathwise, for every realization of the run.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 22, display after (44) ("Add ‖Q0 − Qθ0‖∞ and subtract ‖QK − QθK‖∞ on both sides of (44), it follows that"), with C0 := ‖Q0 − Qθ0‖∞

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Display after (44), p. 22: along every run of Algorithm 1 with step `α ≥ 0` and evaluation
error `ε`, for every `K ≥ 1` and every realization,
`(1/K) ∑_{k=0}^{K−1} ‖Q_k − Q_{θ_k}‖_∞ ≤ C₀/(K(1−γ)) + 2γε/(1−γ)² + 4L_q²α/(1−γ)`, where
`Q_k` is the soft Q-function of `(θ_k, π_k)`, `C₀ = ‖Q₀ − Q_{θ₀}‖_∞` and `L_q = L_r/(1−γ)`. -/
theorem display_after_44 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (ρ : S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Lr Lg : ℝ)
    (h3 : Assumption3 r Lr Lg)
    {m : ℕ} (D : Fin m → Traj S A)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (α ε : ℝ) (hα : 0 ≤ α) (θ₀ : EuclideanSpace ℝ (Fin p)) (π₀ : S → A → ℝ)
    (θ : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (π Qhat : ℕ → Ω → S → A → ℝ)
    (τE τA : ℕ → Ω → Traj S A)
    (hrun : IsMLIRLRun P γ ρ r D Pr ℱ α ε θ₀ π₀ θ π Qhat τE τA)
    (K : ℕ) (hK : 1 ≤ K) (ω : Ω) :
    (1 / (K : ℝ)) * ∑ k ∈ Finset.range K,
        supNorm (softQ P γ r (θ k ω) (π k ω) - optQ P γ r (θ k ω)) ≤
      supNorm (softQ P γ r θ₀ π₀ - optQ P γ r θ₀) / (K * (1 - γ)) +
        2 * γ * ε / (1 - γ) ^ 2 + 4 * (Lr / (1 - γ)) ^ 2 / (1 - γ) * α := by sorry

end StructEstMDP.FiniteTime
