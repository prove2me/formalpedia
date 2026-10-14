-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_display_p24
-- name    : StructEstMDP.FiniteTime.display_p24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:17.838637+00:00
-- url     : https://prove2.me/theorems/28d1630e-f878-4154-9242-1a6cca42b52a
-- title:
--   Display on p. 24 — averaged squared gradient ≤ 2L_cL_q²α + (C₁/K)Σ E[‖Q_{θ_k} − Q_k‖_∞ + ε] + E[(L̂(θ_K) − L̂(θ₀))/(Kα)]
-- statement:
--   Let $(\mathcal S,\mathcal A,P,\rho,\gamma)$ be a finite MDP with $\gamma\in[0,1)$, let the reward satisfy Assumptions 1 and 3 with constants $C_r,L_r,L_g$, let $\mathcal D$ be a nonempty dataset, and let $C_d>0$ be a constant for which the conclusion of Lemma 5 holds. Write
--   $$L_q=\frac{L_r}{1-\gamma},\qquad L_c=\frac{2L_qL_rC_d\sqrt{|\mathcal S|\cdot|\mathcal A|}}{1-\gamma}+\frac{2L_g}{1-\gamma},\qquad C_1=4C_dL_q^2\sqrt{|\mathcal S|\cdot|\mathcal A|}.$$
--   Consider any run of Algorithm 1 on a probability space with step size $\alpha>0$ and policy-evaluation error $\varepsilon$, and let $Q_k$ be the soft Q-function of $(\theta_k,\pi_k)$. Then for every $K\ge1$,
--
--   $$\frac1K\sum_{k=0}^{K-1}\mathbb E\big[\|\nabla_\theta\widehat L(\theta_k;\mathcal D)\|^2\big]\le2L_cL_q^2\alpha+\frac{C_1}{K}\sum_{k=0}^{K-1}\mathbb E\big[\|Q_{\theta_k}-Q_k\|_\infty+\varepsilon\big]+\mathbb E\Big[\frac{\widehat L(\theta_K;\mathcal D)-\widehat L(\theta_0;\mathcal D)}{K\alpha}\Big].$$
--
--   This is the upper-level half of the analysis: summing the ascent inequality (46), the bias bound (48) and the expectation step (47) over the iterations.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 24, display after "Summing the inequality above from k = 0 to K − 1 and dividing both sides by αK, it holds that", with C1 := 4CdL²q√(|S|·|A|)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- The display on p. 24 ("Summing the inequality above from k = 0 to K − 1 and dividing both
sides by αK"): for every constant `C_d` of Lemma 5 and every run of Algorithm 1 with step
`α > 0` and evaluation error `ε` on a probability space, for every `K ≥ 1`,
`(1/K) ∑_{k<K} E‖∇_θ L̂(θ_k; D)‖² ≤ 2 L_c L_q² α + (C₁/K) ∑_{k<K} E[‖Q_{θ_k} − Q_k‖_∞ + ε]
  + E[(L̂(θ_K; D) − L̂(θ₀; D))/(Kα)]`, with `L_q = L_r/(1−γ)`,
`L_c = 2 L_q L_r C_d √(|S|·|A|)/(1−γ) + 2L_g/(1−γ)` and `C₁ = 4 C_d L_q² √(|S|·|A|)`. -/
theorem display_p24 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (ρ : S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hρ : IsDist ρ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Cr Lr Lg : ℝ)
    (h1 : Assumption1 r Cr) (h3 : Assumption3 r Lr Lg)
    {m : ℕ} (D : Fin m → Traj S A) (hm : 0 < m)
    (Cd : ℝ) (hCd0 : 0 < Cd)
    (hCd : ∀ w w' : S → A → ℝ,
      tvDist (visitation P γ ρ (softmax w)) (visitation P γ ρ (softmax w')) ≤
        Cd * frobNorm (w - w'))
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ : Filtration ℕ mΩ)
    (α ε : ℝ) (hα : 0 < α) (θ₀ : EuclideanSpace ℝ (Fin p)) (π₀ : S → A → ℝ)
    (θ : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (π Qhat : ℕ → Ω → S → A → ℝ)
    (τE τA : ℕ → Ω → Traj S A)
    (hrun : IsMLIRLRun P γ ρ r D Pr ℱ α ε θ₀ π₀ θ π Qhat τE τA)
    (K : ℕ) (hK : 1 ≤ K) :
    let Lq := Lr / (1 - γ)
    let Lc := 2 * Lq * Lr * Cd * Real.sqrt (Fintype.card S * Fintype.card A) / (1 - γ) +
      2 * Lg / (1 - γ)
    let C1 := 4 * Cd * Lq ^ 2 * Real.sqrt (Fintype.card S * Fintype.card A)
    (1 / (K : ℝ)) * ∑ k ∈ Finset.range K, ∫ ω, ‖gradient (Lhat P γ ρ r D) (θ k ω)‖ ^ 2 ∂Pr ≤
      2 * Lc * Lq ^ 2 * α +
        C1 / K * ∑ k ∈ Finset.range K,
          ∫ ω, (supNorm (optQ P γ r (θ k ω) - softQ P γ r (θ k ω) (π k ω)) + ε) ∂Pr +
        ∫ ω, (Lhat P γ ρ r D (θ K ω) - Lhat P γ ρ r D (θ 0 ω)) / (K * α) ∂Pr := by sorry

end StructEstMDP.FiniteTime
