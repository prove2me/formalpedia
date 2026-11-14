-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_positive_score_has_maximizing_root
-- name    : StabilityDichotomies.Bijunctive.positive_score_has_maximizing_root
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:37:33.696689+00:00
-- url     : https://prove2.me/theorems/05778170-ba6d-47f6-85d9-9574d293ca30
-- title:
--   A positive literal score is attained by a feasible root
-- statement:
--   If the score of a target literal is positive, then some feasible root reaches it and attains the score, and every other feasible root reaching that literal has score contribution at most this maximum. This realizes the finite maximizers used in the proof of the bijunctive approximation bound.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.positive_score_has_maximizing_root {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (target : Literal V) (hpos : (0 : WithBot ℝ) < literalScore rep G F δ target) :
    ∃ root : Literal V, ∃ n : ℕ, feasibleLiteral F root ∧
      implicationDistance rep G root target = some n ∧
      literalScore rep G F δ target = ((δ root - n : ℝ) : WithBot ℝ) ∧
      ∀ r : Literal V, ∀ m : ℕ, feasibleLiteral F r →
        implicationDistance rep G r target = some m → δ r - m ≤ δ root - n := by
  sorry
