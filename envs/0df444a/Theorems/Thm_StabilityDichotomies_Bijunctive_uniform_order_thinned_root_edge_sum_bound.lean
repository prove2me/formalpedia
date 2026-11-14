-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_uniform_order_thinned_root_edge_sum_bound
-- name    : StabilityDichotomies.Bijunctive.uniform_order_thinned_root_edge_sum_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:08:54.628308+00:00
-- url     : https://prove2.me/theorems/5cceb20e-73da-4e99-91c9-d44cd3a6e922
-- title:
--   Ordered feasible-root prefix edge changes obey the harmonic budget
-- statement:
--   Fix a satisfiable instance, a first-stage occurrence mask, and a finite nonempty family of occurrence indices. For any ordering, form the successive prefixes of added occurrences while holding the first-stage implication graph fixed. The sum over all prefix edges and variables of the feasible-root bit-change probabilities is at most $r_\Gamma|C|H_{2|V|}$. Averaging over all orderings preserves this bound; the formal statement uses unnormalized finite sums.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, inside-first-mask root-deletion averaging.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.uniform_order_thinned_root_edge_sum_bound
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
    (∑ π : Equiv.Perm α, ∑ i : α, cost ((S ((Fintype.equivFin α i).val+1)).image π) (π i)) ≤
      (Fintype.card (Equiv.Perm α) : ℝ) *
        ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)) := by
  sorry
