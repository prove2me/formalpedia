-- Prove2me | Theorems.Thm_RealAPSP_lemma_5_1
-- name    : RealAPSP.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:57:37.554733+00:00
-- url     : https://prove2.me/theorems/48710b79-d692-4601-9aee-28da5d7c89cd
-- title:
--   Lemma 5.1 (Approximation Threshold)
-- statement:
--   Let $A,B,C\in(\mathbb R\cup\{\bot\})^{n\times n}$ and $K\ge1$. There are absolute constants $c_0,C_0>0$ and a randomized algorithm running in time $K(\log(n+2))^{O(1)}$ that with high probability produces one of three outcomes:
--
--   1. an Exact Triangle solution, and there are at least $c_0n^3/K$ exact solutions;
--   2. the answer that the number of $\infty$-approximate solutions is at most $C_0n^3/K$;
--   3. a threshold $\Delta\ge0$ such that the number of $\Delta$-approximate solutions is at most $C_0n^3/K$, and the number of $2\Delta$-approximate solutions is at least $c_0n^3/K$.
--
--   This chooses the scale of the iteration in Theorem 1.1.
--
--   **Formalization Note** The threshold is written as $2\Delta$, the real the proof computes, since the machine has no division.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - reading: randomized algorithm with high probability (§3.1, p.9) → for every failure exponent a there is a program, with the time bound on every tape and correctness on a measurable set of tapes of probability at least 1 − n^{−a}; reason: the p.9 definition, with worst-case time because the page bounds the running time without an expectation
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: real parameters K ≥ 1 → natural numbers K ≥ 1 in input cells; reason: the integer bank cannot read a real; the statement at the floor of a real parameter implies it at that parameter, up to a constant factor in the time
--   - encoding: (log n)^{O(1)} → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - encoding: the threshold ∆ → 2∆ in a real output cell; reason: the proof sets 2∆ := |A[i*,k*] + B[k*,j*] + C[i*,j*]|; the machine has no division
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 5.1, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_RealAPSP_Triangles

namespace RealAPSP

/-- **Lemma 5.1 (Approximation Threshold).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.16 (PDF p.18).

Input: `n`, `K`, then the matrices. The tag at output cell `0` selects the outcome: `1`, an exact solution at output cells `1, 2, 3`, and at least `c₀n³/K` exact solutions; `2`, at most `C₀n³/K`
`∞`-approximate solutions; `3`, real output cell `0` holds `2∆ ≥ 0` with at most `C₀n³/K` `∆`-approximate and at least `c₀n³/K` `2∆`-approximate solutions. The constants `c₀, C₀` are absolute. -/
theorem lemma_5_1 :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∀ a : ℕ, ∃ (P : Program) (κ : ℝ), ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      ∀ A B C : Mat ℝ n,
        RunsWhp P (n + K + 2) (triInts [(n : ℤ), (K : ℤ)] A B C) (triReals [] A B C)
          (κ * (K : ℝ) * Real.log ((n : ℝ) + 2) ^ κ) ((n : ℝ) ^ (-(a : ℝ))) (fun σ =>
            (σ.imem (outCell 0) = 1 ∧
              (∃ i k j, TripleAt σ 1 ((i, k, j) : Triple n) ∧ IsApproxTri 0 A B C i k j) ∧
              c₀ * (n : ℝ) ^ 3 / K ≤ approxCount 0 A B C) ∨
            (σ.imem (outCell 0) = 2 ∧ (presentCount A B C : ℝ) ≤ C₀ * (n : ℝ) ^ 3 / K) ∨
            (σ.imem (outCell 0) = 3 ∧ 0 ≤ σ.rmem (routCell 0) ∧
              (approxCount (σ.rmem (routCell 0) / 2) A B C : ℝ) ≤ C₀ * (n : ℝ) ^ 3 / K ∧
              c₀ * (n : ℝ) ^ 3 / K ≤ approxCount (σ.rmem (routCell 0)) A B C)) := by sorry

end RealAPSP
