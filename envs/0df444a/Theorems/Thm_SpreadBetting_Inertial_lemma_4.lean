-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_4
-- name    : SpreadBetting.Inertial.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:40.381924+00:00
-- url     : https://prove2.me/theorems/e26882e7-18fd-40f4-b7cd-f2f5c8cc5585
-- title:
--   Lemma 4, p. 21 — discrete Dynkin formula: if f(z) = E[u(Y₂)|Y₁ = z] − u(z) then Σ_{s≤t} E f(Y_s) = E u(Y_{t+1}) − E u(Y₁)
-- statement:
--   Let $(Y_t)_{t \ge 1}$ be a time-homogeneous Markov chain on a measurable space $S$ with transition kernel $K$ and an arbitrary initial law. Let $u, f : S \to \mathbb R$ satisfy
--   $$
--   f(z) = \mathbb E[u(Y_2) \mid Y_1 = z] - u(z) = \int u \, dK(z,\cdot) - u(z)\quad\text{for all } z \in S.
--   $$
--   Then for every $t$,
--   $$
--   \mathbb E f(Y_1) + \mathbb E f(Y_2) + \cdots + \mathbb E f(Y_t) = \mathbb E u(Y_{t+1}) - \mathbb E u(Y_1).
--   $$
--
--   This identity is the paper's main tool: solving the difference equation for $u$ turns a $t$-period sum of expectations into two terminal expectations.
--
--   **Formalization Note** The chain is the canonical (Ionescu–Tulcea) process `Kernel.trajMeasure μ₀ (markovChainStep K)`, indexed from $0$, so $Y_{s+1}$ is $\omega_s$. The paper's $S \subset \mathbb R$ is generalized to any measurable space. Added hypotheses, which the paper takes for granted: $u$ is measurable, $u$ is integrable under each $K(z,\cdot)$, and $u(Y_s)$ is integrable for every $s$.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 21, Lemma 4; proof in Appendix F, pp. 47–48

import Mathlib
import Definitions.Def_GittinsIndex

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4 {S : Type*} [MeasurableSpace S] (K : Kernel S S) [IsMarkovKernel K]
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] (u fn : S → ℝ) (hu : Measurable u)
    (huK : ∀ z, Integrable u (K z)) (hf : ∀ z, fn z = (∫ y, u y ∂(K z)) - u z)
    (hint : ∀ s : ℕ, Integrable (fun ω : ℕ → S => u (ω s))
      (Kernel.trajMeasure (X := fun _ => S) μ₀ (BanditAlgorithm.markovChainStep K))) :
    ∀ t : ℕ, ∑ s ∈ Finset.range t,
        ∫ ω, fn (ω s) ∂(Kernel.trajMeasure (X := fun _ => S) μ₀ (BanditAlgorithm.markovChainStep K))
      = (∫ ω, u (ω t) ∂(Kernel.trajMeasure (X := fun _ => S) μ₀ (BanditAlgorithm.markovChainStep K)))
        - ∫ ω, u (ω 0) ∂(Kernel.trajMeasure (X := fun _ => S) μ₀ (BanditAlgorithm.markovChainStep K)) := by sorry

end SpreadBetting.Inertial
