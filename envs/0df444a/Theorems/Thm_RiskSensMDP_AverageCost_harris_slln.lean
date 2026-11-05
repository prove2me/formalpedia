-- Prove2me | Theorems.Thm_RiskSensMDP_AverageCost_harris_slln
-- name    : RiskSensMDP.AverageCost.harris_slln
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T02:15:25.143231+00:00
-- url     : https://prove2.me/theorems/5be310f8-26d4-4e13-8f05-6da72af0b9d1
-- title:
--   Strong law of large numbers for positive Harris chains (Meyn–Tweedie Thm 17.0.1), from every initial state
-- statement:
--   Let $E$ be a standard Borel space and let $P$ be a Markov kernel on $E$. Suppose the chain is **positive Harris recurrent**: it is Harris recurrent with respect to some nonzero $\sigma$-finite measure $\varphi$ and admits an invariant probability measure $\mu$ ($\mu P=\mu$). Let $g:E\to\mathbb R$ be measurable with $\int|g|\,d\mu<\infty$. Then for **every** starting state $x\in E$, the Markov chain $(X_n)_{n\ge0}$ with kernel $P$ and $X_0=x$ satisfies
--
--   $$
--   \lim_{n\to\infty}\frac1n\sum_{k=0}^{n-1} g(X_k)=\int_E g\,d\mu\qquad P_x\text{-almost surely.}
--   $$
--
--   This is the strong law of large numbers for positive Harris chains (Meyn & Tweedie, *Markov Chains and Stochastic Stability*, 2nd ed. 2009, Theorem 17.0.1 (i)). Bäuerle & Rieder invoke it in the proof of Theorem 5.1 to show that the average cost $C^n/n$ of a positive Harris recurrent stationary policy converges almost surely to $\int c(x,f(x))\,\mu_f(dx)$.
--
--   **Formalization Note** $P_x$ is `chainLaw P x`, the Ionescu–Tulcea law of the chain on the path space $E^{\mathbb N}$. Meyn–Tweedie sum $g(\Phi_1),\dots,g(\Phi_n)$; summing $g(X_0),\dots,g(X_{n-1})$ gives the same limit. Standard Borel is assumed in place of Meyn–Tweedie's standing countable-generation hypothesis; the statement holds for any invariant probability $\mu$, which for a Harris recurrent chain is unique.
-- source:
--   Meyn & Tweedie, Markov Chains and Stochastic Stability, 2nd ed. (2009), Theorem 17.0.1 (i); cited in Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes (KIT 1000039663; Math. Oper. Res. 39(1), 2014), p. 17, proof of Theorem 5.1

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Finset

namespace RiskSensMDP.AverageCost

/-- Law of large numbers for positive Harris chains (Meyn & Tweedie 2009, Theorem 17.0.1 (i)). -/
theorem harris_slln {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (P : Kernel E E) [IsMarkovKernel P] (hP : IsPositiveHarrisRecurrent P)
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : Kernel.Invariant P μ)
    (g : E → ℝ) (hg : Measurable g) (hgi : Integrable g μ) (x : E) :
    ∀ᵐ ω ∂(chainLaw P x),
      Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, g (ω k)) atTop
        (nhds (∫ y, g y ∂μ)) := by sorry

end RiskSensMDP.AverageCost
