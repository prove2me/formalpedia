-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_graph_deleted_bit_event_measurable
-- name    : StabilityDichotomies.Bijunctive.graph_deleted_bit_event_measurable
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:24:46.558565+00:00
-- url     : https://prove2.me/theorems/da10f4a1-d154-4953-b656-ddc35eb86aff
-- title:
--   Graph-deletion score decisions are measurable in the full seed
-- statement:
--   The score-comparison event after deleting a fixed occurrence from the graph subinstance, while keeping the original feasibility subinstance, is measurable in the complete priority, cutoff, and shift seed.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Definition 4.8 and proof of Theorem 4.9.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical BigOperators
open MeasureTheory Set StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.graph_deleted_bit_event_measurable {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (j : Fin I.constraints.card) (v : V) :
    MeasurableSet {s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
      literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
        (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,false) <
      literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
        (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,true)} := by
  sorry
