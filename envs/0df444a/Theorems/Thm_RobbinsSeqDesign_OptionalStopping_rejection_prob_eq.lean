-- Prove2me | Theorems.Thm_RobbinsSeqDesign_OptionalStopping_rejection_prob_eq
-- name    : RobbinsSeqDesign.OptionalStopping.rejection_prob_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:21.116982+00:00
-- url     : https://prove2.me/theorems/b3cb1a6d-78df-4c98-8513-5b0ec2329131
-- title:
--   Section 4, Eq. (22) — for a fixed sample size n ≥ 1, P(S_n > αn^{1/2}) = 1 − Φ(α) under H₀
-- statement:
--   Let $x_1,x_2,\dots$ be independent random variables, each normally distributed with mean $0$ and variance $1$ (the null hypothesis $H_0:\theta=0$ of Section 4), and let $S_n=x_1+\cdots+x_n$. The fixed-sample test (21) rejects $H_0$ when $S_n>\alpha n^{1/2}$, where $\alpha$ is a real constant. For every sample size $n\ge 1$ and every real $\alpha$, the probability of rejecting $H_0$ when it is true is
--   $$
--   \varepsilon(\alpha)=P\bigl[S_n>\alpha n^{1/2}\bigr]=1-\Phi(\alpha),
--   $$
--   where $\Phi$ is the standard normal distribution function (23). In particular this error probability does not depend on $n$.
--
--   This is the size of the fixed-sample test; it is the numerator of the optional-stopping bound (25), and the reason the paper says that by choosing $\alpha$ large the error can be made as small as one pleases.
--
--   **Formalization Note.** The paper writes (22) as $\varepsilon(\alpha)=1-\Phi(\alpha)$ for the test (21) at a fixed $n$; the Lean statement makes the probability explicit and requires $n\ge 1$ (at $n=0$ the sum is empty and the event is empty when $\alpha\cdot 0\ge 0$). Normality is `HasLaw (X i) (gaussianReal 0 1) P`, which includes almost-everywhere measurability; independence is `iIndepFun X P`. The numerical example "$\alpha=3.09$ then $\varepsilon(\alpha)\cong .001$" is not formalized.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 534, Section 4, Eqs. (21)–(23)

import Mathlib
import Definitions.Def_RobbinsSeqDesign_OptionalStopping_Setup

namespace RobbinsSeqDesign.OptionalStopping

open MeasureTheory ProbabilityTheory

theorem rejection_prob_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n : ℕ) (hn : 1 ≤ n) (α : ℝ) :
    P.real {ω | α * Real.sqrt n < S X n ω} = 1 - Phi α := by sorry

end RobbinsSeqDesign.OptionalStopping
