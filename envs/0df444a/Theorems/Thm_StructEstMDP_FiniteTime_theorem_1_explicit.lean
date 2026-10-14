-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_theorem_1_explicit
-- name    : StructEstMDP.FiniteTime.theorem_1_explicit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:27.677815+00:00
-- url     : https://prove2.me/theorems/b961936a-be5d-47dc-b371-f0f53bcfdfdb
-- title:
--   Theorem 1 (explicit form, pinned down from its proof, pp. 20–24) — ML-IRL's averaged policy error and averaged squared gradient obey explicit finite-time bounds
-- statement:
--   Let $(\mathcal S,\mathcal A,P,\rho,\gamma)$ be a finite MDP with nonempty finite state and action sets, initial distribution $\rho$ and discount $\gamma\in[0,1)$, satisfying Assumption 2 (geometric mixing under every policy). Then there is a constant $C_d>0$, depending only on $(P,\rho,\gamma)$, with the following property.
--
--   Let the reward $r(s,a;\theta)$, $\theta\in\mathbb R^p$, satisfy Assumptions 1 and 3 with constants $C_r,L_r,L_g$, let $\mathcal D$ be a nonempty dataset of trajectories, $\theta_0$ an initial parameter and $\pi_0$ an initial policy, $K\ge1$, $\alpha_0>0$, $\sigma\in(0,1)$ and $\varepsilon\ge0$. Consider any run of Algorithm 1 (ML-IRL) on a probability space, with step size $\alpha=\alpha_0/K^\sigma$ and policy-evaluation error $\varepsilon$, i.e. $\|\widehat Q_k-Q_k\|_\infty\le\varepsilon$. Write
--   $$L_q=\frac{L_r}{1-\gamma},\quad L_c=\frac{2L_qL_rC_d\sqrt{|\mathcal S|\cdot|\mathcal A|}}{1-\gamma}+\frac{2L_g}{1-\gamma},\quad C_1=4C_dL_q^2\sqrt{|\mathcal S|\cdot|\mathcal A|},\quad C_0=\|Q_0-Q_{\theta_0}\|_\infty,$$
--   where $Q_0$ is the soft Q-function of $(\theta_0,\pi_0)$, and
--   $$B=\frac{C_0}{K(1-\gamma)}+\frac{2\gamma\varepsilon}{(1-\gamma)^2}+\frac{4L_q^2}{1-\gamma}\alpha.$$
--   Then:
--
--   1. for every realization of the run,
--   $$\frac1K\sum_{k=0}^{K-1}\|\log\pi_{k+1}-\log\pi_{\theta_k}\|_\infty\le2\varepsilon+2B;$$
--   2. in expectation,
--   $$\frac1K\sum_{k=0}^{K-1}\mathbb E\big[\|\nabla_\theta\widehat L(\theta_k;\mathcal D)\|^2\big]\le2L_cL_q^2\alpha+C_1(B+\varepsilon)+\frac{\mathbb E\big[\widehat L(\theta_K;\mathcal D)-\widehat L(\theta_0;\mathcal D)\big]}{K\alpha}.$$
--
--   Here $\|\log\pi-\log\pi'\|_\infty=\max_{s,a}|\log\pi(a\mid s)-\log\pi'(a\mid s)|$ and $\pi_\theta$ is the soft-optimal policy. Since $\widehat L$ is bounded under Assumption 1, these bounds give the paper's rates (21a) $O(K^{-1})+O(K^{-\sigma})+O(\varepsilon)$ and (21b) $O(K^{-\sigma})+O(K^{-1+\sigma})+O(K^{-1})+O(\varepsilon)$, and with $\sigma=1/2$ both are $O(K^{-1/2})+O(\varepsilon)$: the single-loop estimator tracks the soft-optimal policy and reaches an approximate stationary point of the surrogate likelihood in finite time.
--
--   **Formalization Note** The printed Theorem 1 states only $O(\cdot)$ rates; this is the explicit pair of inequalities its proof derives ((35) summed with the display after (44), and the display on p. 24 with the display after (44) substituted). Additions and conventions, all disclosed: (i) Theorem 1 prints "Assumptions 1 - 2", but its proof uses Assumption 3 (Lemma 3, Lemma 6, (40)), so Assumption 3 is a hypothesis; (ii) the state space is finite, as the proof's sums over $s\in\mathcal S$ and its constant $\sqrt{|\mathcal S|\cdot|\mathcal A|}$ require; (iii) Algorithm 1's sampling steps are represented by the conditional means of the sampled gradients given the past, the only way the proof uses them; (iv) $\varepsilon\ge0$ allows exact soft policy iteration (the page writes $\epsilon_{\rm app}>0$); (v) part 1 is stated for every realization, which is stronger than the printed expectation; (vi) $C_d$ is chosen before the reward, the data, the horizon and the run, so it is uniform over them; (vii) $\|w-w'\|$ in Lemma 5 is the Frobenius norm.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 12, Theorem 1, (21a)–(21b); explicit form from the proof, §12, pp. 20–24: (35), display after (44) (p. 22), display on p. 24

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Theorem 1 (explicit form, pinned down from its proof, pp. 20–24), p. 12. Under
Assumptions 1–3 there is a constant `C_d > 0`, depending only on `(P, ρ, γ)`, such that every
run of Algorithm 1 with `K ≥ 1` iterations, step `α = α₀/K^σ` (`α₀ > 0`, `σ ∈ (0,1)`) and
policy-evaluation error `ε ≥ 0` satisfies
(a) for every realization,
`(1/K) ∑_{k<K} ‖log π_{k+1} − log π_{θ_k}‖_∞ ≤ 2ε + 2(C₀/(K(1−γ)) + 2γε/(1−γ)² + 4L_q²α/(1−γ))`;
(b) `(1/K) ∑_{k<K} E‖∇_θ L̂(θ_k; D)‖² ≤ 2 L_c L_q² α
  + C₁ (C₀/(K(1−γ)) + 2γε/(1−γ)² + 4L_q²α/(1−γ) + ε) + E[L̂(θ_K; D) − L̂(θ₀; D)]/(Kα)`,
where `L_q = L_r/(1−γ)`, `L_c = 2 L_q L_r C_d √(|S|·|A|)/(1−γ) + 2L_g/(1−γ)`,
`C₁ = 4 C_d L_q² √(|S|·|A|)` and `C₀ = ‖Q₀ − Q_{θ₀}‖_∞`, `Q₀` the soft Q-function of `(θ₀, π₀)`. -/
theorem theorem_1_explicit {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (ρ : S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hρ : IsDist ρ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h2 : Assumption2 P) :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (p : ℕ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Cr Lr Lg : ℝ),
        Assumption1 r Cr → Assumption3 r Lr Lg →
      ∀ (m : ℕ) (D : Fin m → Traj S A), 0 < m →
      ∀ (θ₀ : EuclideanSpace ℝ (Fin p)) (π₀ : S → A → ℝ) (K : ℕ), 1 ≤ K →
      ∀ (α₀ σ ε : ℝ), 0 < α₀ → 0 < σ → σ < 1 → 0 ≤ ε →
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
        (ℱ : Filtration ℕ mΩ)
        (θ : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (π Qhat : ℕ → Ω → S → A → ℝ)
        (τE τA : ℕ → Ω → Traj S A),
        IsMLIRLRun P γ ρ r D Pr ℱ (α₀ / (K : ℝ) ^ σ) ε θ₀ π₀ θ π Qhat τE τA →
        let α := α₀ / (K : ℝ) ^ σ
        let Lq := Lr / (1 - γ)
        let Lc := 2 * Lq * Lr * Cd * Real.sqrt (Fintype.card S * Fintype.card A) / (1 - γ) +
          2 * Lg / (1 - γ)
        let C1 := 4 * Cd * Lq ^ 2 * Real.sqrt (Fintype.card S * Fintype.card A)
        let C0 := supNorm (softQ P γ r θ₀ π₀ - optQ P γ r θ₀)
        let B := C0 / (K * (1 - γ)) + 2 * γ * ε / (1 - γ) ^ 2 + 4 * Lq ^ 2 / (1 - γ) * α
        (∀ ω, (1 / (K : ℝ)) * ∑ k ∈ Finset.range K,
            supNorm (fun s a => Real.log (π (k + 1) ω s a) -
              Real.log (optPolicy P γ r (θ k ω) s a)) ≤ 2 * ε + 2 * B) ∧
        (1 / (K : ℝ)) * ∑ k ∈ Finset.range K, ∫ ω, ‖gradient (Lhat P γ ρ r D) (θ k ω)‖ ^ 2 ∂Pr ≤
          2 * Lc * Lq ^ 2 * α + C1 * (B + ε) +
            (∫ ω, (Lhat P γ ρ r D (θ K ω) - Lhat P γ ρ r D θ₀) ∂Pr) / (K * α) := by sorry

end StructEstMDP.FiniteTime
