-- Prove2me | Theorems.Thm_Sumcheck_short_seed_grid_perfect_cheat
-- name    : Sumcheck.short_seed_grid_perfect_cheat
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:36.386785+00:00
-- url     : https://prove2.me/theorems/f9fb7286-fe2f-46ce-85ad-002d6a49ad8e
-- title:
--   A seed-support lower bound for perfect cheating in mixed-grid sum-check
-- statement:
--   Consider $m$ rounds of sum-check over a finite field, with nonempty summation grids $H_i$ and challenges determined by one seed. Assume honest partial sums have consistent round sums and next-challenge evaluations, and that each degree cap admits both the honest polynomial and degree $2(|H_i|-1)$. If the seed support is smaller than $\prod_{i<m}|H_i|$, then for any initial claim there exists a strategy depending only on the past challenges and current claim that meets every degree and sum test and ends at the true terminal value for every supported seed.
--
--   This gives a necessary lower bound on the number of seeds for soundness in this challenge model when the stated degree caps are available.
-- source:
--   Local derivation: PvsNPGridSumcheckBarrier.lean, short_seed_grid_sumcheck_perfect_cheat. The protocol is the sum-check protocol of Lund, Fortnow, Karloff and Nisan, Algebraic Methods for Interactive Proof Systems. The mixed-grid seed-support result here is the local statement. Original declaration starts at line 193. For the protocol and nonbinary grids see J. Thaler, Proofs, Arguments, and Zero-Knowledge, Section 4.1, Remark 4.1, https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf.

import Mathlib
open Polynomial
open scoped BigOperators

theorem Sumcheck.short_seed_grid_perfect_cheat {F Seed : Type} [Field F] [Fintype F]
    (seeds : Finset Seed) (draw : Seed → ℕ → F) (m : ℕ)
    (H : ℕ → Finset F) (nonempty : ∀ i, (H i).Nonempty) (short : seeds.card < ∏ i ∈ Finset.range m, (H i).card)
    (degree : ℕ → ℕ) (degreeFit : ∀ i, 2*((H i).card-1) ≤ degree i)
    (truth : ∀ i : ℕ, (Fin i → F) → F)
    (honest : ∀ i : ℕ, (Fin i → F) → Polynomial F)
    (honestDegree : ∀ i h, (honest i h).natDegree ≤ degree i)
    (honestSum : ∀ i h, (∑ x ∈ H i, (honest i h).eval x) = truth i h)
    (honestPoint : ∀ s i, (honest i (fun j : Fin i => draw s j.val)).eval (draw s i) =
      truth (i+1) (fun j : Fin (i+1) => draw s j.val))
    (initial : F) :
    ∃ prover : ∀ i : ℕ, (Fin i → F) → F → Polynomial F,
      (∀ i h v, (prover i h v).natDegree ≤ degree i) ∧
      (∀ i h v, (∑ x ∈ H i, (prover i h v).eval x) = v) ∧
      (∀ s ∈ seeds, ∀ run : ℕ → F, run 0 = initial →
        (∀ i, run (i+1) = (prover i (fun j : Fin i => draw s j.val) (run i)).eval (draw s i)) →
        run m = truth m (fun j : Fin m => draw s j.val)) := by sorry
