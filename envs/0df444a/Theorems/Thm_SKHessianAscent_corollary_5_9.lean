-- Prove2me | Theorems.Thm_SKHessianAscent_corollary_5_9
-- name    : SKHessianAscent.corollary_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:16:51.190966+00:00
-- url     : https://prove2.me/theorems/030508d8-079a-4706-8c24-265cc1bfd035
-- title:
--   Corollary 5.9 — diagonal of the squared resolvent: $\|\mathbf E_{\mathcal D_n}[D(aI_n-\beta A+D)^{-2}D]-I_n/(1-\beta^2\mathrm{tr}_n D^{-2})\|_{L^2}\le C\beta/(\gamma_Y^2\sqrt n)$
-- statement:
--   There is a universal constant $C>0$ with the following property. Fix $0<\beta<1$ and $0<\gamma_Y\le\frac{(1-\beta)^4}{4(1+2\beta^2)^2}$. For all $n\ge n_0(\beta,\gamma_Y)$ and $A\sim\mathrm{GOE}(n)$, with probability at least $1-4e^{-n/4}$ the following holds simultaneously for all diagonal matrices $D$ with entries in $[1,\infty)$ satisfying
--
--   $$
--   D^{-1}\big(aI_n-\beta A+D\big)^2D^{-1}\succeq\gamma_YI_n,\qquad a=\beta^2\,\mathrm{tr}_n(D^{-1}):
--   $$
--
--   $$
--   \Big\|\mathbf E_{\mathcal D_n}\big[D\big(\beta^2\mathrm{tr}_n(D^{-1})I_n-\beta A+D\big)^{-2}D\big]-\frac{I_n}{1-\beta^2\mathrm{tr}_n(D^{-2})}\Big\|_{L^2}\le\frac{C\beta}{\gamma_Y^2\sqrt n}.
--   $$
--
--   Here $\mathbf E_{\mathcal D_n}$ is the projection onto diagonal matrices, $\mathrm{tr}_n=\mathrm{Tr}/n$ and $\|X\|_{L^2}=\|X\|_F/\sqrt n$. Moreover, on the same event the bound holds for $D=D(m)$ for every $m\in\mathcal S_{\beta,A}(c)$, for any $c>0$ with $\gamma_Y\le\big(1+\frac{1+3\beta}{c}\big)^{-2}$.
--
--   The corollary says that the diagonal of the weighted squared resolvent is close to its free-probability limit, uniformly over the (random, non-convex) set where the resolvent has a spectral gap; it is the input to the drift and Lipschitz estimates of Section 6.
--
--   **Formalization Note** The set of admissible $D$ depends on $A$, so "uniformly over all $D$" is a universal quantifier inside the event, as in the paper's (6.5). The event of the statement is the conjunction of the two clauses, and the probability bound is on the outer measure of its complement.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Corollary 5.9, eqs. (5.35)–(5.37), p. 35

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem corollary_5_9 :
    ∃ C : ℝ, 0 < C ∧
      ∀ β γ : ℝ, 0 < β → β < 1 → 0 < γ → γ ≤ (1 - β) ^ 4 / (4 * (1 + 2 * β ^ 2) ^ 2) →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          RandMatDisc.goe n {A | ¬ (
              (∀ d : Fin n → ℝ, (∀ i, 1 ≤ d i) →
                ((Matrix.diagonal d)⁻¹ * resolventArg β (Matrix.of A) d ^ 2 * (Matrix.diagonal d)⁻¹
                  - γ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef →
                diagError β (Matrix.of A) d ≤ C * β / (γ ^ 2 * Real.sqrt n)) ∧
              (∀ c : ℝ, 0 < c → γ ≤ ((1 + (1 + 3 * β) / c) ^ 2)⁻¹ →
                ∀ m ∈ safeSet β (Matrix.of A) c,
                  diagError β (Matrix.of A) (fun i => (1 - m i ^ 2)⁻¹) ≤
                    C * β / (γ ^ 2 * Real.sqrt n)))} ≤
            ENNReal.ofReal (4 * Real.exp (-(n : ℝ) / 4)) := by sorry

end SKHessianAscent
