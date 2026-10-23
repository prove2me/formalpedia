-- Prove2me | Theorems.Thm_RLInference_QValueCLT_visit_frequency_tendsto_w
-- name    : RLInference.QValueCLT.visit_frequency_tendsto_w
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:13:08.393815+00:00
-- url     : https://prove2.me/theorems/55af4617-758a-4948-975a-4bb64f7250cb
-- title:
--   Proof of Theorem 1, p. 35, display after (22) — (1/n) Σ_t 1(s_t = i, a_t = j) → w(i, j) a.s.
-- statement:
--   In the setting of (22), let $w$ be a stationary probability vector of the extended chain $\tilde P^\pi((s,a),(s',a'))=P(s'\mid s,a)\pi(a'\mid s')$. This means $w\ge0$, $\sum_x w(x)=1$ and $\sum_x w(x)\tilde P^\pi(x,y)=w(y)$ for all $y$; under irreducibility it is unique. Then almost surely, for every state-action pair $(i,j)$,
--
--   $$\frac1n\sum_{t<n}\mathbb 1(s_t=i,a_t=j)\;\to\;w(i,j)\qquad(n\to\infty).$$
--
--   The long-run visit frequencies are thus the stationary distribution. They are the weights $w$ that enter the asymptotic covariances (8) and (5) through $W^{-1}$.
--
--   **Formalization Note.** The visit count is over the 0-based times $t=0,\dots,n-1$ (the paper's $t=1,\dots,n$). At $n=0$ the ratio is $0/0=0$, which does not affect the limit. The stationary vector is bound by its defining equations rather than constructed. This is faithful because it is unique under Assumption 3.
-- source:
--   Zhu, Dong & Lam, Uncertainty Quantification and Exploration for Reinforcement Learning, arXiv:1910.05471v3, p. 35, App. A.1, display after (22); w defined on p. 9

import Mathlib
import Definitions.Def_RLInference_QValueCLT_Setting
open MeasureTheory ProbabilityTheory Filter Matrix Topology

namespace RLInference.QValueCLT

theorem visit_frequency_tendsto_w {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y)
    (ν₀ : PMF S) :
    ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      ∀ x : S × A, Tendsto (fun n : ℕ => (visits n ω x : ℝ) / n) atTop (𝓝 (w x)) := by sorry

end RLInference.QValueCLT
