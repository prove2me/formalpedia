-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_implication_score_decreases_under_arc_deletion
-- name    : StabilityDichotomies.Bijunctive.implication_score_decreases_under_arc_deletion
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:02:11.535306+00:00
-- url     : https://prove2.me/theorems/195a9c14-6d82-465d-baa8-29beb3a584a3
-- title:
--   Deleting implication arcs cannot increase a literal score
-- statement:
--   Holding the feasible-root set and shifts fixed, deleting arcs from the implication graph cannot increase any literal score. This is the graph-deletion monotonicity used in the sensitivity proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, first step of sensitivity.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.implication_score_decreases_under_arc_deletion {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G G' F : Instance Γ V) (δ : Literal V → ℝ)
    (hsub : ∀ a b, implicationArc rep G' a b → implicationArc rep G a b)
    (target : Literal V) : literalScore rep G' F δ target ≤ literalScore rep G F δ target := by
  sorry
