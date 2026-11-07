-- Prove2me | Theorems.Thm_RealAPSP_lemma_7_5
-- name    : RealAPSP.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:30.51369+00:00
-- url     : https://prove2.me/theorems/7d6c90c2-2f6a-4685-aa4b-bea5e8056f16
-- title:
--   Lemma 7.5 (Reduction from Approximately Low-Rank to Approximately Uniform and Regular Instances)
-- statement:
--   For any $t\ge1$ and $\Delta\ge0$, there is a potential-adjusting reduction from a Real Exact Triangle instance $(A,B,C)$ where one matrix has a given $\Delta$-approximate rank-$r$ decomposition to $t^{875}n^{o(1)}$ instances that are $(r,\Delta)$-uniform and $(1/r,\Delta)$-regular. It runs in time $(rt^{875}n^2+n^3/t)^{1+o(1)}$ and is correct with high probability.
--
--   This is the first half of Lemma 4.5.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - reading: randomized algorithm with high probability (§3.1, p.9) → for every failure exponent a there is a program, with the time bound on every tape and correctness on a measurable set of tapes of probability at least 1 − n^{−a}; reason: the p.9 definition, with worst-case time because the page bounds the running time without an expectation
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: "assume that we also have access to a ∆-approximate rank-r decomposition" (p.11) → the decomposition (U, V, S) is part of the input; reason: as the page says
--   - encoding: rank at most r, with r unrestricted → 1 ≤ r; reason: at r = 0 the matrix is empty, and the printed time bound can be below one step
--   - encoding: real parameters t ≥ 1 → natural numbers t ≥ 1 in input cells; reason: the integer bank cannot read a real; the statement at the floor of a real parameter implies it at that parameter, up to a constant factor in the time
--   - encoding: the exponent 1 + o(1) and the factor n^{o(1)} → functions f, g tending to 0, chosen with the program: time κ·X^{1+f(X)} and count κ·…·n^{g(n)}; reason: the definition of o(1), with the constant κ absorbing small arguments
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 7.5, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_RealAPSP_Rank
import Definitions.Def_RealAPSP_Potential

namespace RealAPSP

/-- **Lemma 7.5 (Reduction from Approximately Low-Rank to Approximately Uniform and Regular Instances).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.32 (PDF p.34). The page's proof defers partly to [Fis26, Lemma 4.10].

Input: `n, r, t, m`, the matrices with `∆`, and a decomposition of the matrix numbered `m`. Output as in `RealAPSP.HasReductionOutput`: a potential-adjusting reduction to at most `κ t^{875} n^{g(n)}` instances that are `(r, ∆)`-uniform and `(1/r, ∆)`-regular. -/
theorem lemma_7_5 :
    ∀ a : ℕ, ∃ (P : Program) (f : ℝ → ℝ) (g : ℕ → ℝ) (κ : ℝ),
      Filter.Tendsto f Filter.atTop (nhds 0) ∧ Filter.Tendsto g Filter.atTop (nhds 0) ∧
      ∀ (n r t : ℕ), 1 ≤ n → 1 ≤ r → 1 ≤ t → ∀ Δ : ℝ, 0 ≤ Δ →
        ∀ (m : Fin 3) (A B C : Mat ℝ n) (U : Fin n → Fin r → ℝ) (V : Fin r → Fin n → ℝ)
          (S : Fin n → Fin n → Option (Fin r)), IsRankDecomp Δ (pick m A B C) r U V S →
        let X : ℝ := (r : ℝ) * (t : ℝ) ^ 875 * (n : ℝ) ^ 2 + (n : ℝ) ^ 3 / t
        RunsWhp P (n + r + t + 2) (triInts [(n : ℤ), (r : ℤ), (t : ℤ), ((m : ℕ) : ℤ)] A B C ++ decompInts S)
          (triReals [Δ] A B C ++ decompReals U V) (κ * X ^ (1 + f X)) ((n : ℝ) ^ (-(a : ℝ)))
          (HasReductionOutput Δ A B C (κ * X ^ (1 + f X)) (κ * (t : ℝ) ^ 875 * (n : ℝ) ^ g n)
            (fun A' B' C' => IsUniform r Δ A' B' C' ∧ IsRegular (1 / (r : ℝ)) Δ A' B' C')) := by sorry

end RealAPSP
