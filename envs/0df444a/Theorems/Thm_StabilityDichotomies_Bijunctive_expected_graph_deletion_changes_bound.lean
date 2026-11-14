-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_expected_graph_deletion_changes_bound
-- name    : StabilityDichotomies.Bijunctive.expected_graph_deletion_changes_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:20:13.08021+00:00
-- url     : https://prove2.me/theorems/381703fc-5162-4f02-b436-61df102dbe7a
-- title:
--   Expected graph-deletion bit changes are logarithmic
-- statement:
--   Fix a satisfiable feasible-root instance, an occurrence-retention mask, and a variable. Under independent rate-$\beta>0$ exponential shifts, the number of occurrence deletions from the graph subinstance that change this variable’s score-comparison output is integrable and has expectation at most $(\log(2|V|)+1)/\beta$. Feasible roots are held fixed throughout this graph-deletion step.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, first sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.expected_graph_deletion_changes_bound {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I F : Instance Γ V) (hF : Satisfiable F)
    (mask : Fin I.constraints.card → Bool) (v : V) (β : ℝ) (hβ : 0 < β) :
    let μ := Measure.pi (fun _ : Literal V => expMeasure β)
    let C := fun δ : Literal V → ℝ => ∑ j : Fin I.constraints.card,
      if decide (literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,false) <
        literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,true)) ≠
          decide (literalScore rep (thinnedInstance I mask) F δ (v,false) <
            literalScore rep (thinnedInstance I mask) F δ (v,true)) then (1 : ℝ) else 0
    Integrable C μ ∧ (∫ δ, C δ ∂μ) ≤ (Real.log (Fintype.card (Literal V)) + 1) / β := by
  sorry
