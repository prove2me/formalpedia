-- Prove2me | Theorems.Thm_SKHessianAscent_theorem_1_1
-- name    : SKHessianAscent.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-23T01:25:55.165478+00:00
-- url     : https://prove2.me/theorems/a6e80d23-304d-4fa0-8202-0081cd116c3f
-- title:
--   Theorem 1.1 (main theorem) — polynomial-time sampling of the SK Gibbs measure with $o_n(1)$ total-variation error at every $\beta<1$
-- statement:
--   Let $0<\beta<1$ and $\delta>0$. Let $A\sim\mathrm{GOE}(n)$ (symmetric, $A_{ij}\sim N(0,1/n)$ for $i<j$, $A_{ii}\sim N(0,2/n)$) and let
--
--   $$
--   \mu_{\beta A}(\sigma)=\frac{1}{Z(\beta A)}\exp\Big(\tfrac12\langle\sigma,\beta A\sigma\rangle\Big),\qquad\sigma\in\{\pm1\}^n,
--   $$
--
--   be the Gibbs measure of the Sherrington–Kirkpatrick model. There is a randomized algorithm, running in time polynomial in $n$, and a sequence $\varepsilon_n\to0$ such that for all $n\ge n_0(\beta,\delta)$, with probability at least $1-\delta$ over $A$, the law $\widehat\mu_A$ of the algorithm's output on input $A$ satisfies
--
--   $$
--   \mathrm{TV}\big(\widehat\mu_A,\mu_{\beta A}\big)\le\varepsilon_n .
--   $$
--
--   The range $\beta<1$ is the whole high-temperature phase of the model, and is believed to be the range in which efficient sampling is possible.
--
--   **Formalization Note** The paper states the theorem for its Algorithm 2, which is assembled from subroutines of two other papers with constants fixed only implicitly; the Lean statement asserts the existence of a sampler with the same guarantee. The sampler is one admissible program (rational literals) of the published `PolySampIso` unit-cost real RAM with Gaussian samples, chosen after $\beta$ and $\delta$ and before $n$; it reads $n$, $\beta$ and $A$ from its input. "Polynomial time" is the bound $C(n+1)^k$ on the number of steps, on every input matrix and all random streams. "With probability at least $1-\delta$" bounds the outer $\mathrm{GOE}(n)$-measure of the set of $A$ with $\mathrm{TV}>\varepsilon_n$ by $\delta$. Total variation is $\tfrac12\sum_\sigma|\widehat\mu_A(\sigma)-\mu_{\beta A}(\sigma)|$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Theorem 1.1, p. 1 (abstract and Algorithm 2, p. 6)

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_PolySampIso_Machine
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Sampler

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem theorem_1_1 (β δ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 < δ) :
    ∃ (P : PolySampIso.Program) (C k : ℕ) (ε : ℕ → ℝ) (n₀ : ℕ),
      PolySampIso.Admissible P ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
        HaltsWithin P (initState n (samplerMem β A)) (C * ((n : ℝ) + 1) ^ k)) ∧
      ∀ n : ℕ, n₀ ≤ n →
        RandMatDisc.goe n {A |
            ε n < lawTV (outLaw P n (initState n (samplerMem β A))) (gibbsSK β (Matrix.of A))} ≤
          ENNReal.ofReal δ := by sorry

end SKHessianAscent
