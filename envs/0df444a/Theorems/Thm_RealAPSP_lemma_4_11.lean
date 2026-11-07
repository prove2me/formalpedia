-- Prove2me | Theorems.Thm_RealAPSP_lemma_4_11
-- name    : RealAPSP.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:30.558925+00:00
-- url     : https://prove2.me/theorems/2bb906d7-467b-44d0-a890-2cb187160185
-- title:
--   Lemma 4.11 (Listing-to-Decision for Integer Negative Triangle, [VWW18])
-- statement:
--   If Integer Negative Triangle is decided in time $O(n^{3-\varepsilon}(\log(u+2))^d)$ with $\varepsilon>0$, then there is $d'$ such that for each $T\ge1$ one lists $\min(T,\#\text{solutions})$ distinct solutions in time $O(n^{3-\varepsilon}T^{\varepsilon/3}(\log(u+2))^{d'})$.
--
--   The listing bound is how the reduction turns few nonpositive integer triangles into a small running time.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: (log u)^{O(1)} → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - encoding: up to T solutions, with T unrestricted → 1 ≤ T; reason: "up to 0 solutions" in time 0 is not a claim of the page
--   - reading: "list up to T solutions" → min(T, number of solutions) distinct solutions, deterministically; reason: it must find them all when there are fewer; the hypothesis and the reduction are deterministic
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 4.11, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RealAPSP_Problems

namespace RealAPSP

/-- **Lemma 4.11 (Listing-to-Decision for Integer Negative Triangle, [VWW18]).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.15 (PDF p.17).

A deterministic program lists `min(T, #solutions)` distinct solutions in time `O(n^{3−ε} T^{ε/3} (log(u+2))^{d'})`: the count at output cell `0`, the triples from output cell `1`. -/
theorem lemma_4_11 :
    ∀ (ε : ℝ) (d : ℕ), 0 < ε → IntNegTriDecided ε d →
      ∃ (d' : ℕ) (P : Program) (κ : ℝ), ∀ (n u T : ℕ), 1 ≤ n → 1 ≤ T → ∀ X Y Z : Mat ℤ n,
        WeightsBounded u X → WeightsBounded u Y → WeightsBounded u Z →
        Runs P ((n + T + 2) * (u + 2)) (intTriInts [(n : ℤ), (u : ℤ), (T : ℤ)] X Y Z) []
          (κ * (n : ℝ) ^ (3 - ε) * (T : ℝ) ^ (ε / 3) * Real.log ((u : ℝ) + 2) ^ d') (fun σ =>
            let m := (σ.imem (outCell 0)).toNat
            m = min T (negCount (castMat X) (castMat Y) (castMat Z)) ∧
            ∃ τ : Fin m → Triple n, Function.Injective τ ∧
              ∀ l : Fin m, TripleAt σ (1 + 3 * (l : ℕ)) (τ l) ∧
                IsNegTri (castMat X) (castMat Y) (castMat Z) (τ l).1 (τ l).2.1 (τ l).2.2) := by sorry

end RealAPSP
