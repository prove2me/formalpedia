-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_deletion_graph_feasibility_cost_split
-- name    : StabilityDichotomies.Bijunctive.bijunctive_deletion_graph_feasibility_cost_split
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:47:37.565284+00:00
-- url     : https://prove2.me/theorems/ee224f99-8528-4c94-85b1-d1929eed6b20
-- title:
--   Bijunctive deletion sensitivity splits into graph and feasible-root costs
-- statement:
--   For one constraint occurrence, the exact-law Wasserstein distance is bounded by the sum of two shared-seed bit-change costs. The first removes its implication arcs while retaining the original feasible-root set. The second then removes it from the feasible-root instance while retaining the reduced graph. Occurrences are indexed separately, including duplicates.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, two-step deletion coupling.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_deletion_graph_feasibility_cost_split {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (j : Fin I.constraints.card) (ε : ℝ) (hε : 0 < ε)
    (A : Solver Γ) (hLaw : BijunctiveOutputLaw Γ rep ε A)
    (e : Fin I.constraints.card ≃ Option (Fin (I.delete (occurrenceAt I j)).constraints.card))
    (hej : e j = none)
    (he : ∀ k, (e k).elim (occurrenceAt I j) (occurrenceAt (I.delete (occurrenceAt I j))) = occurrenceAt I k) :
    let μ := bijunctiveSeedMeasure rep I ε
    let G := fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j))
    let F := fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))
    let Fminus := fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1) && decide (i ≠ j))
    let mid := fun z v => decide (literalScore rep (G z) (F z) z.2.2 (v,false) < literalScore rep (G z) (F z) z.2.2 (v,true))
    let last := fun z v => decide (literalScore rep (G z) (Fminus z) z.2.2 (v,false) < literalScore rep (G z) (Fminus z) z.2.2 (v,true))
    wasserstein (A V I) (A V (I.delete (occurrenceAt I j))) ≤
      (∑ v : V, (μ {z | bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v ≠ mid z v}).toReal) +
      (∑ v : V, (μ {z | mid z v ≠ last z v}).toReal) := by
  sorry
