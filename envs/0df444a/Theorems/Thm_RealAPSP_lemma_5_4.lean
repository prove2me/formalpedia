-- Prove2me | Theorems.Thm_RealAPSP_lemma_5_4
-- name    : RealAPSP.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:18.127283+00:00
-- url     : https://prove2.me/theorems/195e3344-61a8-4368-a1a8-92b4fb058016
-- title:
--   Lemma 5.4 (Popular Instances Have Low Rank)
-- statement:
--   Let $\Delta\ge0$, $L\ge1$ and $A,B,C\in(\mathbb R\cup\{\bot\})^{n\times n}$, where each $C$-edge $(i,j)$ with $C[i,j]\ne\bot$ is in at least $n/L$ $\Delta$-approximate solutions. Then with high probability one computes a $\Delta$-approximate decomposition of $C$ of rank at most $\kappa_1L\log(n+2)$, in time $O(Ln^2\log(n+2))$.
--
--   So popular edges form a low-rank matrix, on which the reduction to integers applies.
--
--   **Formalization Note** The rank is an output of the run.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - reading: randomized algorithm with high probability (§3.1, p.9) → for every failure exponent a there is a program, with the time bound on every tape and correctness on a measurable set of tapes of probability at least 1 − n^{−a}; reason: the p.9 definition, with worst-case time because the page bounds the running time without an expectation
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: real parameters L ≥ 1 → natural numbers L ≥ 1 in input cells; reason: the integer bank cannot read a real; the statement at the ceiling of a real L implies it at L: the hypothesis on L implies the one on ⌈L⌉, and the bounds at ⌈L⌉ ≤ 2L are within the O-constants
--   - encoding: log n → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - reading: "we can compute" → a randomized algorithm correct with high probability; reason: the printed proof samples k uniformly at random and closes with "with high probability"; the rank constant may depend on the failure exponent, as Θ(L log n) iterations are what give it
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 5.4, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_RealAPSP_Rank

namespace RealAPSP

/-- **Lemma 5.4 (Popular Instances Have Low Rank).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.18 (PDF p.20).

Input: `n`, `L`, then `∆` and the matrices. The output is a `∆`-approximate decomposition of `C`, with its rank `R ≤ κ₁·L·log(n+2)` at output cell `0`. The page's "we can compute" is randomized by its proof. -/
theorem lemma_5_4 :
    ∀ a : ℕ, ∃ (P : Program) (κ₁ κ₂ : ℝ), ∀ (n L : ℕ), 1 ≤ n → 1 ≤ L → ∀ Δ : ℝ, 0 ≤ Δ → ∀ A B C : Mat ℝ n,
      (∀ i j, (C i j).isSome = true → (n : ℝ) / L ≤ edgeCountC Δ A B C i j) →
      RunsWhp P (n + L + 2) (triInts [(n : ℤ), (L : ℤ)] A B C) (triReals [Δ] A B C)
        (κ₂ * (L : ℝ) * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 2)) ((n : ℝ) ^ (-(a : ℝ))) (fun σ =>
          let R := (σ.imem (outCell 0)).toNat
          (R : ℝ) ≤ κ₁ * (L : ℝ) * Real.log ((n : ℝ) + 2) ∧ HasRankOutput Δ C R 1 σ) := by sorry

end RealAPSP
