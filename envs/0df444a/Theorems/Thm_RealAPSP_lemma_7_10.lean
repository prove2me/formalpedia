-- Prove2me | Theorems.Thm_RealAPSP_lemma_7_10
-- name    : RealAPSP.lemma_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:22.464193+00:00
-- url     : https://prove2.me/theorems/78934ab7-136f-4081-b4f8-ad89e8c43af9
-- title:
--   Lemma 7.10 (Reduction from Approx. Uniform Regular to Approx. Uniform Low-Doubling Instances)
-- statement:
--   Let $\Delta\ge0$ and $K\ge1$. There is a potential-adjusting reduction from a Real Exact Triangle instance $(A,B,C)$ that is $(D,\Delta)$-uniform and $(1/D,\Delta)$-regular to $O(K^{1/56})$ instances that are $(D,\Delta)$-uniform and $(K,\Delta)$-doubling. It runs in time $\tilde O(n^2K^{1/56}+n^3/K^{1/56})$ and is correct with high probability.
--
--   This is the second half of Lemma 4.5, resting on a BSG covering theorem for approximate reals.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - reading: randomized algorithm with high probability (§3.1, p.9) → for every failure exponent a there is a program, with the time bound on every tape and correctness on a measurable set of tapes of probability at least 1 − n^{−a}; reason: the p.9 definition, with worst-case time because the page bounds the running time without an expectation
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: real parameters K and D ≥ 1 → natural numbers K and D ≥ 1 in input cells; reason: the integer bank cannot read a real; the statement at the floor of a real parameter implies it at that parameter, up to a constant factor in the time
--   - encoding: the polylog of Õ → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - encoding: D unrestricted → 1 ≤ D; reason: 1/D is undefined at D = 0
--   - encoding: output instances that are restrictions → the general output format of a potential-adjusting reduction; reason: a restriction is the case of potentials 0
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 7.10, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_RealAPSP_Potential

namespace RealAPSP

/-- **Lemma 7.10 (Reduction from Approx. Uniform Regular to Approx. Uniform Low-Doubling Instances).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.36 (PDF p.38).

Input: `n, K, D`, then `∆` and the matrices. Output as in `RealAPSP.HasReductionOutput`: a potential-adjusting reduction to at most `κK^{1/56}` instances that are `(D, ∆)`-uniform and `(K, ∆)`-doubling. The output instances of the page's proof are restrictions; the output format keeps potentials, which may be `0`. -/
theorem lemma_7_10 :
    ∀ a : ℕ, ∃ (P : Program) (κ : ℝ), ∀ (n K D : ℕ), 1 ≤ n → 1 ≤ K → 1 ≤ D → ∀ Δ : ℝ, 0 ≤ Δ → ∀ A B C : Mat ℝ n,
      IsUniform D Δ A B C → IsRegular (1 / (D : ℝ)) Δ A B C →
      let X : ℝ := (n : ℝ) ^ 2 * (K : ℝ) ^ ((1 : ℝ) / 56) + (n : ℝ) ^ 3 / (K : ℝ) ^ ((1 : ℝ) / 56)
      RunsWhp P (n + K + D + 2) (triInts [(n : ℤ), (K : ℤ), (D : ℤ)] A B C) (triReals [Δ] A B C)
        (κ * X * Real.log ((n : ℝ) + K + 2) ^ κ) ((n : ℝ) ^ (-(a : ℝ)))
        (HasReductionOutput Δ A B C (κ * X * Real.log ((n : ℝ) + K + 2) ^ κ) (κ * (K : ℝ) ^ ((1 : ℝ) / 56))
          (fun A' B' C' => IsUniform D Δ A' B' C' ∧ IsDoubling (K : ℝ) Δ A' B' C')) := by sorry

end RealAPSP
