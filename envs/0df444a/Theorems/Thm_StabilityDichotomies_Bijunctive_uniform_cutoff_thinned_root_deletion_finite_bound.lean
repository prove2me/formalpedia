-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_uniform_cutoff_thinned_root_deletion_finite_bound
-- name    : StabilityDichotomies.Bijunctive.uniform_cutoff_thinned_root_deletion_finite_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:07:15.007861+00:00
-- url     : https://prove2.me/theorems/16a3b46a-93f7-49d9-9fbd-7b7f3fd33920
-- title:
--   Uniform cutoff averaging bounds actual thinned feasible-root deletion costs
-- statement:
--   Fix a satisfiable instance, a first-stage occurrence mask, and a finite nonempty family of occurrence indices to add in a uniformly random order. Hold the first-stage implication graph fixed and draw independent exponential shifts. For a uniformly chosen cutoff prefix, sum the bit-change probabilities from deleting each retained added occurrence. The average over orderings and cutoffs is at most $r_\Gamma|C|H_{2|V|}$. The displayed formal version uses the equivalent unnormalized finite sums.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, outside-first-mask root-deletion averaging.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.uniform_cutoff_thinned_root_deletion_finite_bound
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (m : Fin I.constraints.card → Bool) (σ : α → Fin I.constraints.card) (β : ℝ) (hβ : 0 < β) :
    let S := fun t : ℕ => Finset.univ.filter (fun a : α => (Fintype.equivFin α a).val < t)
    let mask := fun (A : Finset α) (i : Fin I.constraints.card) => m i || decide (∃ a ∈ A, σ a = i)
    let bit := fun (A : Finset α) (δ : Literal V → ℝ) (v : V) =>
      decide (literalScore rep (thinnedInstance I m) (thinnedInstance I (mask A)) δ (v,false) <
        literalScore rep (thinnedInstance I m) (thinnedInstance I (mask A)) δ (v,true))
    let cost := fun (A : Finset α) (a : α) => ∑ v : V,
      (Measure.pi (fun _ : Literal V => expMeasure β) {δ | bit A δ v ≠ bit (A.erase a) δ v}).toReal
    (∑ q : Fin (Fintype.card α + 1), ∑ π : Equiv.Perm α,
      ∑ i ∈ S q.val, cost ((S q.val).image π) (π i)) ≤
      (Fintype.card α + 1 : ℝ) * (Fintype.card (Equiv.Perm α) : ℝ) *
        ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)) := by
  sorry
