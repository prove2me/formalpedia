-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_disjoint_subsets_maxima_close_probability
-- name    : StabilityDichotomies.Bijunctive.disjoint_subsets_maxima_close_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:42:06.739196+00:00
-- url     : https://prove2.me/theorems/8050dc39-b1fb-4bd5-a1dc-2379c3311851
-- title:
--   Close maxima on disjoint subsets of independent shifted exponentials
-- statement:
--   For disjoint nonempty subsets $S,T$ of a finite index set, let each $Z_i$ be an independent rate-$\beta$ exponential variable minus a fixed real offset. For $r\ge0$, the probability that the maxima on $S$ and $T$ differ by at most $r$ is at most $1-e^{-\beta r}$. Variables indexed outside $S\cup T$ do not affect the event.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Mathlib
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set

theorem StabilityDichotomies.Bijunctive.disjoint_subsets_maxima_close_probability {α : Type} [Fintype α] (s t : Finset α)
    (hs : s.Nonempty) (ht : t.Nonempty) (hdis : Disjoint s t)
    (β r : ℝ) (hβ : 0 < β) (hr : 0 ≤ r) (d : α → ℝ) :
    ((Measure.pi (fun _ : α => expMeasure β)) {δ : α → ℝ | ∃ a ∈ s, ∃ b ∈ t, (∀ k ∈ s, δ k - d k ≤ δ a - d a) ∧ (∀ k ∈ t, δ k - d k ≤ δ b - d b) ∧ (δ a - d a) - (δ b - d b) ≤ r ∧ (δ b - d b) - (δ a - d a) ≤ r}).toReal ≤
      1 - Real.exp (-β*r) := by
  sorry
