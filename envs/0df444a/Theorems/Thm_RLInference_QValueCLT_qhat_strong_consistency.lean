-- Prove2me | Theorems.Thm_RLInference_QValueCLT_qhat_strong_consistency
-- name    : RLInference.QValueCLT.qhat_strong_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:13:00.488817+00:00
-- url     : https://prove2.me/theorems/8f441beb-afb6-4e4d-9e36-e23f21e1264b
-- title:
--   Proof of Theorem 1, p. 36 — φ(μ̂_{R,n}, P̂_n) − φ(μ_R, P) → 0 a.s., i.e. Q̂_n → Q a.s.
-- statement:
--   Under Assumptions 1, 2 and 3, with $0\le\gamma<1$, the plug-in Q-value estimate is strongly consistent. Let the data be the Markov chain collected under $\pi$ from an arbitrary initial state law, and let $p^0(\cdot\mid s,a)$ be probability vectors. Then almost surely
--
--   $$\hat Q_n=\operatorname{Fix}(\gamma,\hat\mu_{R,n},\hat P_n)\;\to\;Q=\operatorname{Fix}(\gamma,\mu_R,P)\qquad(n\to\infty).$$
--
--   In the proof of Theorem 1 this follows from (22) and the continuity of $\phi$. It is the first conclusion of Theorem 1.
--
--   **Formalization Note.** Assumption 2 is the strict-argmax hypothesis on a bound map $a^*$, and Assumption 3 is irreducibility of $\tilde P^\pi$. The discount $0\le\gamma<1$ is implicit in the paper (p. 7) and pinned here.
-- source:
--   Zhu, Dong & Lam, Uncertainty Quantification and Exploration for Reinforcement Learning, arXiv:1910.05471v3, p. 36, App. A.1, display after "Now, from (22), by continuous mapping theorem"

import Mathlib
import Definitions.Def_RLInference_QValueCLT_Setting
open MeasureTheory ProbabilityTheory Filter Matrix Topology

namespace RLInference.QValueCLT

theorem qhat_strong_consistency {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
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
    (ν₀ : PMF S) :
    ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      Tendsto (fun n => QHat γ u0 p0 n ω) atTop (𝓝 (bellmanFix γ (muR R) (Pmat P))) := by sorry

end RLInference.QValueCLT
