-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_isolated_variable_graph_deletion_score_unchanged
-- name    : StabilityDichotomies.Bijunctive.isolated_variable_graph_deletion_score_unchanged
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:27:41.648876+00:00
-- url     : https://prove2.me/theorems/a7bd8fe1-4a89-494b-b097-c8fb481e0325
-- title:
--   Isolated variables have graph-independent literal scores
-- statement:
--   If a variable lies outside every original constraint scope, then with feasible roots and shifts fixed, both of its literal scores are the same for every occurrence-thinned implication graph. Consequently graph-step deletions cannot change that variable’s output.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, first sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.isolated_variable_graph_deletion_score_unchanged {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I F : Instance Γ V) (v : V)
    (hiso : ∀ c ∈ I.constraints, ∀ k : Fin c.rel.val.arity, c.scope k ≠ v)
    (mask mask' : Fin I.constraints.card → Bool) (δ : Literal V → ℝ) (b : Bool) :
    literalScore rep (thinnedInstance I mask) F δ (v,b) =
      literalScore rep (thinnedInstance I mask') F δ (v,b) := by
  sorry
