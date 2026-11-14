-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_score_assignment_stable_if_winning_distance_preserved
-- name    : StabilityDichotomies.Bijunctive.score_assignment_stable_if_winning_distance_preserved
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:03:34.147222+00:00
-- url     : https://prove2.me/theorems/3c8afe56-d695-4547-8ab2-ca6529bc401a
-- title:
--   Preserving a winning path preserves the output bit after arc deletion
-- statement:
--   Hold feasible roots and shifts fixed and delete implication arcs. If a root attaining the original winning literal score retains its original finite distance to that literal, the algorithm output on that variable is unchanged. The statement handles the score-comparison tie rule exactly.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, first step of sensitivity.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.score_assignment_stable_if_winning_distance_preserved {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G G' F : Instance Γ V) (δ : Literal V → ℝ)
    (hsub : ∀ a b, implicationArc rep G' a b → implicationArc rep G a b)
    (v : V) (w : Bool) (root : Literal V) (n : ℕ)
    (hw : w = decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)))
    (hroot : feasibleLiteral F root)
    (hmax : literalScore rep G F δ (v,w) = ((δ root - n : ℝ) : WithBot ℝ))
    (hd : implicationDistance rep G' root (v,w) = some n) :
    decide (literalScore rep G' F δ (v,false) < literalScore rep G' F δ (v,true)) = w := by
  sorry
