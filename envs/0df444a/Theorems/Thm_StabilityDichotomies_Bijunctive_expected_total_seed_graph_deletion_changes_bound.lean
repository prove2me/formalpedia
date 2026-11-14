-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_expected_total_seed_graph_deletion_changes_bound
-- name    : StabilityDichotomies.Bijunctive.expected_total_seed_graph_deletion_changes_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:29:54.398203+00:00
-- url     : https://prove2.me/theorems/7c4bb634-ce76-492e-a7b7-e6a1e16c3f83
-- title:
--   Total graph-deletion changes satisfy the source sensitivity bound
-- statement:
--   Under the complete Definition 4.8 seed law for a satisfiable instance, fix the random feasible-root set and sum Hamming changes over all occurrence deletions from the random graph subinstance. The count is integrable and its expectation is at most $r_\Gamma |\mathcal C|(\log(2|V|)+1)/\beta$, where $r_\Gamma$ is the maximum relation arity and $\beta=\varepsilon/(2b_\Gamma)$. Isolated variables contribute zero.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-deletion sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.expected_total_seed_graph_deletion_changes_bound {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (ε : ℝ) (hε : 0 < ε) :
    let μ := bijunctiveSeedMeasure rep I ε
    let C := fun (v : V) (s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) =>
      ∑ j : Fin I.constraints.card,
        if decide (literalScore rep
          (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,false) <
          literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,true)) ≠
          bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v then (1 : ℝ) else 0
    Integrable (fun s => ∑ v, C v s) μ ∧
      (∫ s, ∑ v, C v s ∂μ) ≤ (maxArity Γ * I.constraints.card : ℕ) *
        ((Real.log (Fintype.card (Literal V)) + 1) / bijunctiveRate rep ε) := by
  sorry
