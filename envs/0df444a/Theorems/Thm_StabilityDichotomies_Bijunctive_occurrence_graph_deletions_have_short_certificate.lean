-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_occurrence_graph_deletions_have_short_certificate
-- name    : StabilityDichotomies.Bijunctive.occurrence_graph_deletions_have_short_certificate
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:10:54.127503+00:00
-- url     : https://prove2.me/theorems/1e9c0877-227f-4ae8-8969-ea2a6177692f
-- title:
--   Sensitive occurrence deletions lie on a short winning-path certificate
-- statement:
--   For the actual occurrence-indexed thinned implication graph, all occurrence deletions that can change a variable’s output with fixed feasible roots lie in a finite set of at most $n$ occurrences, where $n$ is strictly less than a feasible maximizing root’s shift. Equal constraint values remain distinct indexed occurrences.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-deletion sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.occurrence_graph_deletions_have_short_certificate
    {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I F : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (δ : Literal V → ℝ) (v : V) (w : Bool)
    (hw : w = decide (literalScore rep (thinnedInstance I mask) F δ (v,false) <
      literalScore rep (thinnedInstance I mask) F δ (v,true)))
    (hpos : (0 : WithBot ℝ) < literalScore rep (thinnedInstance I mask) F δ (v,w)) :
    ∃ root : Literal V, ∃ n : ℕ, ∃ S : Finset (Fin I.constraints.card),
      S.card ≤ n ∧ (n : ℝ) < δ root ∧
      ∀ j ∉ S, decide (literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,false) <
        literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,true)) = w := by
  sorry
