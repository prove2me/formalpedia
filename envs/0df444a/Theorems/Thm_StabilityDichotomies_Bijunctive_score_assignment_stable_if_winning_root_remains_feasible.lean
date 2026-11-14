-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_score_assignment_stable_if_winning_root_remains_feasible
-- name    : StabilityDichotomies.Bijunctive.score_assignment_stable_if_winning_root_remains_feasible
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:22:18.047202+00:00
-- url     : https://prove2.me/theorems/ea106b4f-e596-4de4-8833-b49d21d7efc9
-- title:
--   A winning root that remains feasible preserves the output bit
-- statement:
--   With graph and shifts fixed, adding feasibility constraints does not change a variable’s output if an original maximizing root for its winning literal remains feasible. The result includes ties in the exact score-comparison rule.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.score_assignment_stable_if_winning_root_remains_feasible {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F F' : Instance Γ V) (δ : Literal V → ℝ)
    (hsub : ∀ c ∈ F.constraints, c ∈ F'.constraints)
    (v : V) (w : Bool) (root : Literal V) (n : ℕ)
    (hw : w = decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)))
    (hroot : feasibleLiteral F' root)
    (hmax : literalScore rep G F δ (v,w) = ((δ root - n : ℝ) : WithBot ℝ))
    (hd : implicationDistance rep G root (v,w) = some n) :
    decide (literalScore rep G F' δ (v,false) < literalScore rep G F' δ (v,true)) = w := by
  sorry
