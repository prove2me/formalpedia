-- Prove2me | Theorems.Thm_RobbinsSeqDesign_OptionalStopping_optional_stopping_window_bound
-- name    : RobbinsSeqDesign.OptionalStopping.optional_stopping_window_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:30.713083+00:00
-- url     : https://prove2.me/theorems/1e9bfe45-0be2-4012-b092-e988e7887470
-- title:
--   Section 4, Eq. (25) — g(n₁, n₂, α) < (1 − Φ(α))/(1 − Φ(α(λ^{1/2} − 1)/(λ − 1)^{1/2})), λ = n₂/n₁
-- statement:
--   Let $x_1,x_2,\dots$ be independent random variables, each normal with mean $0$ and variance $1$, and $S_n=x_1+\cdots+x_n$. For integers $1\le n_1<n_2$ and a real constant $\alpha$ let
--   $$
--   g(n_1,n_2,\alpha)=P\bigl[S_n>\alpha n^{1/2}\ \text{for some } n_1\le n\le n_2\bigr]
--   $$
--   be the probability that the fixed-sample test (21) rejects at some sample size of the window (24), and put $\lambda=n_2/n_1>1$. Then
--   $$
--   g(n_1,n_2,\alpha)<\frac{1-\Phi(\alpha)}{1-\Phi\!\Bigl(\alpha\cdot\dfrac{\lambda^{1/2}-1}{(\lambda-1)^{1/2}}\Bigr)},
--   $$
--   where $\Phi$ is the standard normal distribution function (23).
--
--   A statistician who allows the sample size to be chosen anywhere in $[n_1,n_2]$ thus controls the probability of wrongly rejecting $H_0$ by the fixed-sample error $1-\Phi(\alpha)$ inflated by a factor depending only on $\alpha$ and the ratio $\lambda$; the paper notes the bound is useful when $\lambda$ is not too large.
--
--   **Formalization Note.** The inequality is strict, as printed. The paper's range of the parameters is made explicit: $n_1\ge 1$ (so that $\lambda=n_2/n_1$ is defined) and $n_1<n_2$ (so that $\lambda>1$ and $(\lambda-1)^{1/2}\ne 0$); $\lambda$ is the real quotient $n_2/n_1$. No sign condition is put on $\alpha$: the paper's $\alpha$ is "some constant", and the inequality holds for every real $\alpha$ (for $\alpha\le 0$ the right side is at least $1$ while $g<1$). The window includes both endpoints $n_1$ and $n_2$. The remarks "useful when $\lambda$ is not too large" and "sharper inequalities can no doubt be devised" are not formalized.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 535, Section 4, Eqs. (24), (25)

import Mathlib
import Definitions.Def_RobbinsSeqDesign_OptionalStopping_Setup

namespace RobbinsSeqDesign.OptionalStopping

open MeasureTheory ProbabilityTheory

theorem optional_stopping_window_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁)
    (hn₁₂ : n₁ < n₂) (α : ℝ) :
    g P X n₁ n₂ α <
      (1 - Phi α) /
        (1 - Phi (α * ((Real.sqrt ((n₂ : ℝ) / n₁) - 1) / Real.sqrt ((n₂ : ℝ) / n₁ - 1)))) := by sorry

end RobbinsSeqDesign.OptionalStopping
