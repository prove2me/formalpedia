-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_positive_score_has_short_winning_path
-- name    : StabilityDichotomies.Bijunctive.positive_score_has_short_winning_path
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:05:10.540228+00:00
-- url     : https://prove2.me/theorems/503e7bab-79ce-4a8f-9767-90b4da85a17b
-- title:
--   A positive winning score has a short maximizing path
-- statement:
--   A positive literal score is attained by a feasible root whose shortest-path length is strictly less than that root’s shift. This is the path-length estimate used in the first sensitivity step.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph deletion step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.positive_score_has_short_winning_path {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (target : Literal V) (hpos : (0 : WithBot ℝ) < literalScore rep G F δ target) :
    ∃ root : Literal V, ∃ n : ℕ, feasibleLiteral F root ∧
      implicationDistance rep G root target = some n ∧
      literalScore rep G F δ target = ((δ root - n : ℝ) : WithBot ℝ) ∧
      (n : ℝ) < δ root := by
  sorry
