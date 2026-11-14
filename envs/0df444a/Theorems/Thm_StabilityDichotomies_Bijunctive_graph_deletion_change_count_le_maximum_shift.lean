-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_graph_deletion_change_count_le_maximum_shift
-- name    : StabilityDichotomies.Bijunctive.graph_deletion_change_count_le_maximum_shift
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:17:24.961796+00:00
-- url     : https://prove2.me/theorems/d39878a7-06ed-4249-9189-91e70414c3b6
-- title:
--   Graph-step bit changes are bounded by the maximum shift
-- statement:
--   For a satisfiable feasible-root instance and positive literal shifts, fix a variable and an occurrence-retention mask. Across all occurrence deletions from the graph subinstance, the number that change its output bit with feasible roots fixed is at most the maximum literal shift. This is a deterministic graph-step sensitivity estimate.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-deletion sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.graph_deletion_change_count_le_maximum_shift
    {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I F : Instance Γ V) (hF : Satisfiable F)
    (mask : Fin I.constraints.card → Bool) (δ : Literal V → ℝ) (hδ : ∀ a, 0 < δ a) (v : V) :
    let G := thinnedInstance I mask
    let bit := decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true))
    let changed := Finset.univ.filter (fun j : Fin I.constraints.card =>
      decide (literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,false) <
        literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,true)) ≠ bit)
    (changed.card : ℝ) ≤ max 0 (Finset.univ.sup' Finset.univ_nonempty δ) := by
  sorry
