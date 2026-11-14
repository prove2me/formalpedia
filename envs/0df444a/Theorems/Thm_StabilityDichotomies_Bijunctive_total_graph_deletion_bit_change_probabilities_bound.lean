-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_total_graph_deletion_bit_change_probabilities_bound
-- name    : StabilityDichotomies.Bijunctive.total_graph_deletion_bit_change_probabilities_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:49:20.790118+00:00
-- url     : https://prove2.me/theorems/5e9af65e-7c9a-41b6-9a8d-138d3468ffe6
-- title:
--   Total graph-only deletion disagreement probabilities obey the source bound
-- statement:
--   Sum, over all constraint occurrences and variables, the shared-seed probabilities that deleting only the occurrence’s implication arcs changes the output bit. This total is bounded by $r_\Gamma |C|(\log(2|V|)+1)/\beta$, with the source exponential rate $\beta$. The probability form connects the proved graph-change estimate to the Wasserstein coupling split.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-only deletion bound.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.total_graph_deletion_bit_change_probabilities_bound {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I) (ε : ℝ) (hε : 0 < ε) :
    let μ := bijunctiveSeedMeasure rep I ε
    let mid := fun (j : Fin I.constraints.card) (z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) v =>
      decide (literalScore rep (thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))) z.2.2 (v,false) <
        literalScore rep (thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))) z.2.2 (v,true))
    (∑ j : Fin I.constraints.card, ∑ v : V,
      (μ {z | bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v ≠ mid j z v}).toReal) ≤
    (maxArity Γ * I.constraints.card : ℕ) *
      ((Real.log (Fintype.card (Literal V)) + 1) / bijunctiveRate rep ε) := by
  sorry
