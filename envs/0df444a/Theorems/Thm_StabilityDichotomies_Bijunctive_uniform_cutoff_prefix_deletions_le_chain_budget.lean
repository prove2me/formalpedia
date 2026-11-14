-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_uniform_cutoff_prefix_deletions_le_chain_budget
-- name    : StabilityDichotomies.Bijunctive.uniform_cutoff_prefix_deletions_le_chain_budget
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:59:16.700796+00:00
-- url     : https://prove2.me/theorems/b811dd41-0e8f-4d81-92b8-be3919d23f23
-- title:
--   Uniform cutoff averaging bounds all prefix deletions by the chain budget
-- statement:
--   Take a uniform random ordering and a uniform cutoff among its possible prefixes. Suppose the sum of the consecutive last-edge costs in every ordering is at most $B$. For any nonnegative set-dependent deletion costs, the expected sum over all elements retained by the cutoff is at most $B$. The formal finite-sum statement also permits any family of prefix sets of the requisite sizes.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, outside-mask deletion symmetry.

import Mathlib
open scoped Classical BigOperators

theorem StabilityDichotomies.Bijunctive.uniform_cutoff_prefix_deletions_le_chain_budget
    {α τ : Type} [Fintype α] [DecidableEq α] [Fintype τ]
    (S : τ → Finset α) (last : τ → α) (cost : τ → Finset α → α → ℝ) (B : ℝ)
    (hsize : ∀ q, (S q).card ≤ Fintype.card τ)
    (hlast : ∀ q, S q ≠ ∅ → last q ∈ S q)
    (hnonneg : ∀ q π, 0 ≤ cost q ((S q).image π) (π (last q)))
    (hchain : ∀ π : Equiv.Perm α,
      (∑ q : τ, if S q = ∅ then 0 else cost q ((S q).image π) (π (last q))) ≤ B) :
    (∑ q : τ, ∑ π : Equiv.Perm α, ∑ i ∈ S q, cost q ((S q).image π) (π i)) ≤
      (Fintype.card τ : ℝ) * (Fintype.card (Equiv.Perm α) : ℝ) * B := by
  sorry
