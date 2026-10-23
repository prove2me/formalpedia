-- Prove2me | Theorems.Thm_RLInference_QValueCLT_eq_22_plugin_consistency
-- name    : RLInference.QValueCLT.eq_22_plugin_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:12:59.344988+00:00
-- url     : https://prove2.me/theorems/58e53292-49ad-4a94-9a1f-978caae549c2
-- title:
--   (22), p. 35 — under Assumptions 1 and 3, [μ̂_{R,n}, P̂_n] → [μ_R, P] a.s.
-- statement:
--   Let $\mathcal S,\mathcal A$ be finite nonempty sets, $P(\cdot\mid s,a)$ a transition law, $R(s,a)$ reward laws on $\mathbb R$ with finite second moments (Assumption 1), and $\pi$ an exploration policy whose extended chain $\tilde P^\pi$ is irreducible (Assumption 3). This means for all pairs $x,y$ there is $m\ge0$ with $(\tilde P^\pi)^m(x,y)>0$. Let the data $((s_t,a_t),r_t)_{t\ge0}$ be the Markov chain collected under $\pi$, started from an arbitrary initial state law $\nu_0$. Let the fallback values $u^0$ be arbitrary and $p^0(\cdot\mid s,a)$ be probability vectors. Then almost surely
--
--   $$\hat\mu_{R,n}\to\mu_R\quad\text{and}\quad\hat P_n\to P\qquad(n\to\infty),$$
--
--   entrywise, where $\hat\mu_{R,n}$ and $\hat P_n$ are the sample mean reward (2) and the empirical transition matrix (3).
--
--   This is the strong consistency of the plug-in parameters, the first step of the proof of Theorem 1. Combined with continuity of the Bellman fixed point it gives $\hat Q_n\to Q$ almost surely.
--
--   **Formalization Note.** The data law is the Markov chain on $(\mathcal S\times\mathcal A)\times\mathbb R$ with kernel $((s,a),r)\mapsto\sum_{s',a'}P(s'\mid s,a)\pi(a'\mid s')\,\delta_{(s',a')}\otimes R(s',a')$, and the conclusion holds for every initial law. Assumption 1 is `MemLp id 2 (R x)`; its independence clause is built into the kernel.
-- source:
--   Zhu, Dong & Lam, Uncertainty Quantification and Exploration for Reinforcement Learning, arXiv:1910.05471v3, p. 35, App. A.1, display (22)

import Mathlib
import Definitions.Def_RLInference_QValueCLT_Setting
open MeasureTheory ProbabilityTheory Filter Matrix Topology

namespace RLInference.QValueCLT

theorem eq_22_plugin_consistency {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (u0 : S × A → ℝ) (p0 : S × A → S → ℝ)
    (hp0_nonneg : ∀ x k, 0 ≤ p0 x k) (hp0_sum : ∀ x, ∑ k, p0 x k = 1)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (ν₀ : PMF S) :
    ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      Tendsto (fun n => muHat u0 n ω) atTop (𝓝 (muR R)) ∧
      Tendsto (fun n => PHat p0 n ω) atTop (𝓝 (Pmat P)) := by sorry

end RLInference.QValueCLT
