-- Prove2me | Theorems.Thm_RealAPSP_lemma_4_5
-- name    : RealAPSP.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:15.783386+00:00
-- url     : https://prove2.me/theorems/9b723496-a885-4185-a978-9ad51077d785
-- title:
--   Lemma 4.5 (Reduction to Approximately Uniform and Low-Doubling Weights)
-- statement:
--   Let $s\ge1$, $\Delta\ge0$ and let $(A,B,C)$ be an Exact Triangle instance where one of the matrices has a given $\Delta$-approximate rank-$r$ decomposition. There is a $\Delta$-approximate potential-adjusting reduction, running in time $(rsn^2+n^3/s^{1/10^5})^{1+o(1)}$, to $sn^{o(1)}$ instances where for each instance the set of weights $X$ satisfies, with high probability:
--
--   1. (Approximate Uniformity) $|X|_{\pm\Delta}\le r$;
--   2. (Approximate Low-Doubling) $|X+X|_{\pm\Delta}\le s\,|X|_{\pm\Delta}\le sr$.
--
--   This puts the weights in the shape Poor Man's Freiman's theorem accepts.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - reading: randomized algorithm with high probability (§3.1, p.9) → for every failure exponent a there is a program, with the time bound on every tape and correctness on a measurable set of tapes of probability at least 1 − n^{−a}; reason: the p.9 definition, with worst-case time because the page bounds the running time without an expectation
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: "assume that we also have access to a ∆-approximate rank-r decomposition" (p.11) → the decomposition (U, V, S) is part of the input; reason: as the page says
--   - encoding: rank at most r, with r unrestricted → 1 ≤ r; reason: at r = 0 the matrix is empty, and the printed time bound can be below one step
--   - encoding: real parameters s ≥ 1 → natural numbers s ≥ 1 in input cells; reason: the integer bank cannot read a real; the statement at the floor of a real parameter implies it at that parameter, up to a constant factor in the time
--   - encoding: the exponent 1 + o(1) and the factor n^{o(1)} → functions f, g tending to 0, chosen with the program: time κ·X^{1+f(X)} and count κ·…·n^{g(n)}; reason: the definition of o(1), with the constant κ absorbing small arguments
--   - encoding: |𝒯| ≤ T for the time T (Definition 4.4) → the same bound, stated as a clause of the output; reason: the definition asks for it
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 4.5, p.12 (PDF p.14); restated p.38 (PDF p.40)

import Mathlib
import Definitions.Def_RealAPSP_Rank
import Definitions.Def_RealAPSP_Potential

namespace RealAPSP

/-- **Lemma 4.5 (Reduction to Approximately Uniform and Low-Doubling Weights).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.12 (PDF p.14); restated p.38 (PDF p.40).

Input: `n, r, s, m`, the matrices with `∆`, and a decomposition of the matrix numbered `m`. Output as in `RealAPSP.HasReductionOutput`: a `∆`-approximate potential-adjusting reduction to at most `κ s n^{g(n)}` instances, each `(r, ∆)`-uniform and `(s, ∆)`-doubling. The second inequality
`s·|X|_{±∆} ≤ sr` of the page follows from uniformity. -/
theorem lemma_4_5 :
    ∀ a : ℕ, ∃ (P : Program) (f : ℝ → ℝ) (g : ℕ → ℝ) (κ : ℝ),
      Filter.Tendsto f Filter.atTop (nhds 0) ∧ Filter.Tendsto g Filter.atTop (nhds 0) ∧
      ∀ (n r s : ℕ), 1 ≤ n → 1 ≤ r → 1 ≤ s → ∀ Δ : ℝ, 0 ≤ Δ →
        ∀ (m : Fin 3) (A B C : Mat ℝ n) (U : Fin n → Fin r → ℝ) (V : Fin r → Fin n → ℝ)
          (S : Fin n → Fin n → Option (Fin r)), IsRankDecomp Δ (pick m A B C) r U V S →
        let X : ℝ := (r : ℝ) * s * (n : ℝ) ^ 2 + (n : ℝ) ^ 3 / (s : ℝ) ^ ((1 : ℝ) / 10 ^ 5)
        RunsWhp P (n + r + s + 2) (triInts [(n : ℤ), (r : ℤ), (s : ℤ), ((m : ℕ) : ℤ)] A B C ++ decompInts S)
          (triReals [Δ] A B C ++ decompReals U V) (κ * X ^ (1 + f X)) ((n : ℝ) ^ (-(a : ℝ)))
          (HasReductionOutput Δ A B C (κ * X ^ (1 + f X)) (κ * (s : ℝ) * (n : ℝ) ^ g n)
            (fun A' B' C' => IsUniform r Δ A' B' C' ∧ IsDoubling (s : ℝ) Δ A' B' C')) := by sorry

end RealAPSP
