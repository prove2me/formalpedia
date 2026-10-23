-- Prove2me | Theorems.Thm_RLInference_QValueCLT_theorem_1_q_value_clt
-- name    : RLInference.QValueCLT.theorem_1_q_value_clt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:13:04.291977+00:00
-- url     : https://prove2.me/theorems/40192638-9632-41ec-b919-2234a437c968
-- title:
--   Theorem 1, p. 10 — Q̂_n → Q a.s. and √n(Q̂_n − Q) ⇒ N(0, Σ), Σ = (I − γP̃^{π*})⁻¹W⁻¹(D_R + γ²D_Q)((I − γP̃^{π*})⁻¹)ᵀ
-- statement:
--   **Theorem 1** (Zhu, Dong and Lam). Consider a finite MDP with nonempty state space $\mathcal S$ and action space $\mathcal A$, transition law $P$, reward laws $R(s,a)$ and discount factor $0\le\gamma<1$. Assume:
--   1. **Assumption 1:** each $R(s,a)$ has finite mean $\mu_R(s,a)$ and finite variance $\sigma^2_R(s,a)$, and rewards are independent of the next state given $(s,a)$;
--   2. **Assumption 2:** the Q-values $Q=\operatorname{Fix}(\gamma,\mu_R,P)$, the fixed point of the Bellman equation (1), have a unique maximizer $a^*(s)$ in every state;
--   3. **Assumption 3:** the data are collected by an exploration policy $\pi$ whose extended chain $\tilde P^\pi((s,a),(s',a'))=P(s'\mid s,a)\pi(a'\mid s')$ is irreducible, with stationary distribution $w$.
--
--   Let $\hat Q_n=\operatorname{Fix}(\gamma,\hat\mu_{R,n},\hat P_n)$ be the plug-in estimate built from $n$ observations by (2)–(3), with any initial values $u^0$ and probability vectors $p^0$. Then $\hat Q_n\to Q$ almost surely, and
--
--   $$\sqrt n\,(\hat Q_n-Q)\;\Rightarrow\;\mathcal N(0,\Sigma)\qquad(n\to\infty),$$
--
--   where
--
--   $$\Sigma=(I-\gamma\tilde P^{\pi^*})^{-1}W^{-1}(D_R+\gamma^2D_Q)\big((I-\gamma\tilde P^{\pi^*})^{-1}\big)^T.$$
--
--   Here $\tilde P^{\pi^*}((s,a),(s',a'))=P(s'\mid s,a)\mathbb 1(a'=a^*(s'))$, and $W$, $D_R$, $D_Q$ are the $N\times N$ diagonal matrices with entries $w(s,a)$, $\sigma^2_R(s,a)$ and $(V^*)^T\Sigma_{P_{s,a}}V^*$, with $V^*(s)=\max_aQ(s,a)$ and $\Sigma_{P_{s,a}}$ the multinomial covariance (4).
--
--   The theorem gives asymptotically exact confidence regions for all Q-values at once. Its explicit covariance is what the paper's exploration policy (Q-OCBA) optimizes.
--
--   **Formalization Note.** The data are the Markov chain $((s_t,a_t),r_t)$ under $\pi$ (kernel described in the Setting definition), started from an arbitrary initial state law $\nu_0$; the conclusions hold for every $\nu_0$. Assumption 2 is the strict inequality $Q(s,a)<Q(s,a^*(s))$ for $a\ne a^*(s)$. Assumption 3 is $\forall x,y\ \exists m,\ (\tilde P^\pi)^m(x,y)>0$, and $w$ is bound by the stationarity equations (unique under Assumption 3). $0\le\gamma<1$ is implicit in the paper and pinned. The Gaussian limit is Mathlib's `multivariateGaussian 0 Σ` on `EuclideanSpace ℝ (S × A)`, and convergence in distribution is `TendstoInDistribution`.
-- source:
--   Zhu, Dong & Lam, Uncertainty Quantification and Exploration for Reinforcement Learning, arXiv:1910.05471v3, p. 10, Theorem 1, (5)–(6); proof App. A.1, pp. 35–36

import Mathlib
import Definitions.Def_RLInference_QValueCLT_Setting
open MeasureTheory ProbabilityTheory Filter Matrix Topology

namespace RLInference.QValueCLT

theorem theorem_1_q_value_clt {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (u0 : S × A → ℝ) (p0 : S × A → S → ℝ)
    (hp0_nonneg : ∀ x k, 0 ≤ p0 x k) (hp0_sum : ∀ x, ∑ k, p0 x k = 1)
    (aStar : S → A)
    (hAstar : ∀ (s : S) (a : A), a ≠ aStar s →
      bellmanFix γ (muR R) (Pmat P) (s, a) < bellmanFix γ (muR R) (Pmat P) (s, aStar s))
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y)
    (ν₀ : PMF S) :
    (∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      Tendsto (fun n => QHat γ u0 p0 n ω) atTop (𝓝 (bellmanFix γ (muR R) (Pmat P)))) ∧
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (WithLp.toLp 2
            (fun x => Real.sqrt n * (QHat γ u0 p0 n ω x - bellmanFix γ (muR R) (Pmat P) x)) :
          EuclideanSpace ℝ (S × A)))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (multivariateGaussian 0
        (SigmaQ γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))) (sigma2R R) w)) := by sorry

end RLInference.QValueCLT
