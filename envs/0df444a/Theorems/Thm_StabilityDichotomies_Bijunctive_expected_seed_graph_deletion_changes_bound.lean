-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_expected_seed_graph_deletion_changes_bound
-- name    : StabilityDichotomies.Bijunctive.expected_seed_graph_deletion_changes_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:26:28.224397+00:00
-- url     : https://prove2.me/theorems/c844fda1-f5e3-4d28-a2cd-7866380632bd
-- title:
--   Graph-deletion bit changes under the full bijunctive seed law
-- statement:
--   Under the full Definition 4.8 priority, cutoff, and exponential-shift seed law for a satisfiable input, fix a variable. Keeping the random feasible-root instance fixed, sum the changes in that bit over deletion of each occurrence from the random graph subinstance. This count is integrable and has expectation at most $(\log(2|V|)+1)/\beta$, where $\beta=\varepsilon/(2b_\Gamma)$.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, first sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.expected_seed_graph_deletion_changes_bound {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (ε : ℝ) (hε : 0 < ε) (v : V) :
    let μ := bijunctiveSeedMeasure rep I ε
    let C := fun s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      ∑ j : Fin I.constraints.card,
        if decide (literalScore rep
          (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,false) <
          literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,true)) ≠
          bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v then (1 : ℝ) else 0
    Integrable C μ ∧ (∫ s, C s ∂μ) ≤
      (Real.log (Fintype.card (Literal V)) + 1) / bijunctiveRate rep ε := by
  sorry
