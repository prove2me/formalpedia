-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_two_group_maxima_close_probability
-- name    : StabilityDichotomies.Bijunctive.two_group_maxima_close_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:36:47.569811+00:00
-- url     : https://prove2.me/theorems/e2f4c640-889e-4559-bc37-156231530f63
-- title:
--   Close maxima of two groups of shifted exponentials
-- statement:
--   Let $S,T$ partition a finite index set into two nonempty groups, and let $Z_i$ be independent rate-$\beta$ exponential variables minus fixed real offsets. For $r\ge0$, the probability that the maxima of the two groups differ by at most $r$ is at most $1-e^{-\beta r}$. This is the shifted-exponential estimate used for the violation probability of a retained non-unit clause.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Mathlib
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set

theorem StabilityDichotomies.Bijunctive.two_group_maxima_close_probability {α : Type} [Fintype α] (s t : Finset α)
    (hs : s.Nonempty) (ht : t.Nonempty) (hdis : Disjoint s t) (hcover : s ∪ t = Finset.univ)
    (β r : ℝ) (hβ : 0 < β) (hr : 0 ≤ r) (d : α → ℝ) :
    ((Measure.pi (fun _ : α => expMeasure β))
      {δ : α → ℝ | ∃ a ∈ s, ∃ b ∈ t,
        (∀ k ∈ s, δ k - d k ≤ δ a - d a) ∧
        (∀ k ∈ t, δ k - d k ≤ δ b - d b) ∧
        (δ a - d a) - (δ b - d b) ≤ r ∧
        (δ b - d b) - (δ a - d a) ≤ r}).toReal ≤ 1 - Real.exp (-β*r) := by
  sorry
