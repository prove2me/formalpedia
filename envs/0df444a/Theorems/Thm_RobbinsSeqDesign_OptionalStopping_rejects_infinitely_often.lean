-- Prove2me | Theorems.Thm_RobbinsSeqDesign_OptionalStopping_rejects_infinitely_often
-- name    : RobbinsSeqDesign.OptionalStopping.rejects_infinitely_often
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:16.776167+00:00
-- url     : https://prove2.me/theorems/4c2892c9-47c8-4792-a9ac-81531562b15e
-- title:
--   Section 4, p. 534 — with probability 1, S_n > αn^{1/2} for infinitely many n, however large α
-- statement:
--   Let $x_1,x_2,\dots$ be independent standard normal random variables and $S_n=x_1+\cdots+x_n$. For every real constant $\alpha$, with probability $1$ the rejection inequality (21),
--   $$
--   S_n>\alpha n^{1/2},
--   $$
--   holds for infinitely many values of $n$.
--
--   This is the fact that makes optional stopping dangerous: an experimenter who samples until (21) is verified is almost surely going to stop and reject the true hypothesis $H_0$, whatever value of $\alpha$ the statistician chose. The paper deduces it from the law of the iterated logarithm.
--
--   **Formalization Note.** "With probability 1 … for infinitely many values of $n$" is `∀ᵐ ω ∂P, ∃ᶠ n in atTop, α * √n < S n ω`. The statement is for every real $\alpha$ ("no matter how large the value of $\alpha$").
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 534, Section 4 (consequence of the law of the iterated logarithm, unnumbered)

import Mathlib
import Definitions.Def_RobbinsSeqDesign_OptionalStopping_Setup

namespace RobbinsSeqDesign.OptionalStopping

open MeasureTheory ProbabilityTheory Filter

theorem rejects_infinitely_often {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∃ᶠ n : ℕ in atTop, α * Real.sqrt n < S X n ω := by sorry

end RobbinsSeqDesign.OptionalStopping
