-- Prove2me | Theorems.Thm_RealAPSP_lemma_6_1
-- name    : RealAPSP.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:35.022662+00:00
-- url     : https://prove2.me/theorems/5f4e9f94-cb15-4b8a-b644-b3961cdb803f
-- title:
--   Lemma 6.1 (Detecting Very Negative Triangles In Low-Rank Instances)
-- statement:
--   Assume Integer APSP is solved in time $O(n^{3-\varepsilon}(\log(u+2))^d)$, with $\varepsilon>0$. Let $\Delta\ge0$, and let $(A,B,C)$ be a Real Negative Triangle instance along with a $\Delta$-approximate rank-$r$ decomposition of $C$. Then there is a deterministic algorithm in time $\tilde O(rn^{3-\varepsilon})$ that either outputs a negative triangle in $(A,B,C)$ or reports that every triangle has weight at least $-\Delta$.
--
--   After this step every negative triangle is a $\Delta$-approximate exact triangle, so the listing machinery for exact triangles applies. This is what makes the APSP reduction lose $\varepsilon^3$ rather than $\varepsilon^2$.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: "assume that we also have access to a ∆-approximate rank-r decomposition" (p.11) → the decomposition (U, V, S) is part of the input; reason: as the page says
--   - encoding: rank at most r, with r unrestricted → 1 ≤ r; reason: at r = 0 the matrix is empty, and the printed time bound can be below one step
--   - encoding: the polylog of Õ → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - reading: "There is an algorithm" → a deterministic run on the all-false tape; reason: the printed proof is deterministic given the hypothesis of Theorem 1.1
--   - reading: (log u)^{O(1)} as an assumption → a fixed exponent d in the hypothesis, the constants of the conclusion chosen after d and ε; reason: the printed O(1) depends on d through the assumed algorithm
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 6.1, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_RealAPSP_Problems
import Definitions.Def_RealAPSP_Rank

namespace RealAPSP

/-- **Lemma 6.1 (Detecting Very Negative Triangles In Low-Rank Instances).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.21 (PDF p.23).

Assume the hypothesis of Theorem 1.1 for `ε, d`. A deterministic program in time `Õ(rn^{3−ε})` either sets output cell `0` to `1` and writes a negative triangle at output cells `1, 2, 3`, or sets it to `0`, and then every triangle has weight at least `−∆`. -/
theorem lemma_6_1 (ε : ℝ) (hε : 0 < ε) (d : ℕ) (h : IntegerAPSPSolved ε d) :
    ∃ (P : Program) (κ : ℝ), ∀ (n r : ℕ), 1 ≤ n → 1 ≤ r → ∀ Δ : ℝ, 0 ≤ Δ →
      ∀ (A B C : Mat ℝ n) (U : Fin n → Fin r → ℝ) (V : Fin r → Fin n → ℝ) (S : Fin n → Fin n → Option (Fin r)),
        IsRankDecomp Δ C r U V S →
        Runs P (n + r + 2) (triInts [(n : ℤ), (r : ℤ)] A B C ++ decompInts S) (triReals [Δ] A B C ++ decompReals U V)
          (κ * (r : ℝ) * (n : ℝ) ^ (3 - ε) * Real.log ((n : ℝ) + r + 2) ^ κ) (fun σ =>
            (σ.imem (outCell 0) = 1 ∧ ∃ i k j, TripleAt σ 1 ((i, k, j) : Triple n) ∧ IsNegTri A B C i k j) ∨
            (σ.imem (outCell 0) = 0 ∧ ∀ i k j x, triSum A B C i k j = some x → -Δ ≤ x)) := by sorry

end RealAPSP
