-- Prove2me | Theorems.Thm_RealAPSP_lemma_5_2
-- name    : RealAPSP.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:10.504965+00:00
-- url     : https://prove2.me/theorems/af5b87e4-ad32-4586-a991-5fe0b2b46cd1
-- title:
--   Lemma 5.2 (Popular/Unpopular Decomposition)
-- statement:
--   Let $A,B,C\in(\mathbb R\cup\{\bot\})^{n\times n}$, $\Delta\ge0$ and $L\ge1$. A randomized algorithm in time $\tilde O(n^2L^2)$ partitions the edge set into popular and unpopular edges such that with high probability:
--
--   1. each popular edge is in at least $n/L$ $2\Delta$-approximate solutions;
--   2. there are at most $6n^3/L$ $2\Delta$-approximate solutions involving unpopular edges.
--
--   Popular edges have low rank by Lemma 5.4, and unpopular edges carry few solutions, which is what the proof of Theorem 1.1 separates.
--
--   **Formalization Note** One bit per entry of each matrix; a ⊥ entry is not popular.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - reading: randomized algorithm with high probability (§3.1, p.9) → for every failure exponent a there is a program, with the time bound on every tape and correctness on a measurable set of tapes of probability at least 1 − n^{−a}; reason: the p.9 definition, with worst-case time because the page bounds the running time without an expectation
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: the parameter L ≥ 1, a real → L real, given to the program as L and the unit 1 in real cells and ⌈L⌉ in an integer cell; reason: the thresholds compare counts with n/L, which needs a real unit since the only real literal is 0; ⌈L⌉ sets the sample count and the word bound; the constant 1 is no instance data, and every real L ≥ 1 is covered
--   - encoding: the polylog of Õ → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 5.2, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_RealAPSP_Triangles

namespace RealAPSP

/-- **Lemma 5.2 (Popular/Unpopular Decomposition).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.17 (PDF p.19).

Input: `n` and `⌈L⌉` in integer cells; `∆`, `L`, the unit `1`, then the matrices in real cells. The parameter `L ≥ 1` is real, as on the page, since the constant `6` and the threshold `n/L` are exact. For matrix `mat` (`0`, `1`, `2` for `A`, `B`, `C`), output cell `mat·n² + x·n + y` is `1` exactly for a popular edge. The time is `Õ(n²L²)`. -/
theorem lemma_5_2 :
    ∀ a : ℕ, ∃ (P : Program) (κ : ℝ), ∀ (n : ℕ) (L : ℝ), 1 ≤ n → 1 ≤ L → ∀ Δ : ℝ, 0 ≤ Δ → ∀ A B C : Mat ℝ n,
      RunsWhp P (n + ⌈L⌉₊ + 2) (triInts [(n : ℤ), ((⌈L⌉₊ : ℕ) : ℤ)] A B C) (triReals [Δ, L, 1] A B C)
        (κ * (n : ℝ) ^ 2 * L ^ 2 * Real.log ((n : ℝ) + L + 2) ^ κ) ((n : ℝ) ^ (-(a : ℝ))) (fun σ =>
          let pop : Marking n := fun mat x y =>
            σ.imem (outCell ((mat : ℕ) * (n * n) + (x : ℕ) * n + y)) = 1
          (∀ i k, pop 0 i k → (A i k).isSome = true ∧ (n : ℝ) / L ≤ edgeCountA (2 * Δ) A B C i k) ∧
          (∀ k j, pop 1 k j → (B k j).isSome = true ∧ (n : ℝ) / L ≤ edgeCountB (2 * Δ) A B C k j) ∧
          (∀ i j, pop 2 i j → (C i j).isSome = true ∧ (n : ℝ) / L ≤ edgeCountC (2 * Δ) A B C i j) ∧
          (unpopularCount (2 * Δ) pop A B C : ℝ) ≤ 6 * (n : ℝ) ^ 3 / L) := by sorry

end RealAPSP
