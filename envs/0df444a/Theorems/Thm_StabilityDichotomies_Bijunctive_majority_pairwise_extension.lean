-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_majority_pairwise_extension
-- name    : StabilityDichotomies.Bijunctive.majority_pairwise_extension
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:49:07.087934+00:00
-- url     : https://prove2.me/theorems/2131f244-f667-4f6b-b898-8017890737c6
-- title:
--   Majority-closed Boolean relations are determined by their binary projections
-- statement:
--   Let R be a nonempty finite relation on Boolean tuples, closed under coordinatewise majority. If a Boolean tuple x has the property that every pair of its coordinates is matched by some tuple of R, then x itself belongs to R. This two-decomposability property is the key construction step for fixed two-CNF representations of bijunctive relations.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, use of two-CNF representations in §4.2.2, p. 19, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem StabilityDichotomies.Bijunctive.majority_pairwise_extension {ι : Type} [Fintype ι] (R : Finset (ι → Bool))
    (hR : R.Nonempty) (hmajority : ∀ a b c, a ∈ R → b ∈ R → c ∈ R →
      (fun i => (a i && b i) || (a i && c i) || (b i && c i)) ∈ R)
    (x : ι → Bool) (hpairs : ∀ i j : ι, ∃ y ∈ R, y i = x i ∧ y j = x j) : x ∈ R := by sorry
