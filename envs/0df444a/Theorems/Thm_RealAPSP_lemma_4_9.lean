-- Prove2me | Theorems.Thm_RealAPSP_lemma_4_9
-- name    : RealAPSP.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:57.984782+00:00
-- url     : https://prove2.me/theorems/a69356c2-f6d1-4e04-bca5-a218a49828bc
-- title:
--   Lemma 4.9 (Real-to-Integer Reduction for Low-Rank Reals)
-- statement:
--   Let $\Delta\ge0$, $s\ge1$, and let $A,B,C\in(\mathbb R\cup\{\bot\})^{n\times n}$, where one of the matrices has a given $\Delta$-approximate rank-$r$ decomposition. There is an algorithm running in time
--
--   $$\bigl((rs)^{O(1)}n^2+n^3/s^{1/10^5}\bigr)^{1+o(1)}$$
--
--   that reports a set of triangles $\mathcal T$ and outputs $sn^{o(1)}$ triples of integer matrices $X,Y,Z$, with entries in $[\pm2^{(s\log(r+2))^{O(1)}}]\cup\{\bot\}$, such that with high probability, for every $T$ bounding the number of $2\Delta$-approximate exact triangles of $(A,B,C)$:
--
--   1. $|\mathcal T|\le T$, and the number of exact triangles in any $(X,Y,Z)$ is at most $T$;
--   2. any $\Delta$-approximate exact triangle in $(A,B,C)$ is in $\mathcal T$ or an exact triangle in some $(X,Y,Z)$;
--   3. any negative triangle $(i,k,j)$ in some $(X,Y,Z)$ satisfies $A[i,k]+B[k,j]+C[i,j]<2\Delta$.
--
--   This is the single way the real-to-integer tools enter the main proof: low-rank real triangles are replaced by integer instances, which the assumed algorithm then lists.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - reading: randomized algorithm with high probability (§3.1, p.9) → for every failure exponent a there is a program, with the time bound on every tape and correctness on a measurable set of tapes of probability at least 1 − n^{−a}; reason: the p.9 definition, with worst-case time because the page bounds the running time without an expectation
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: "assume that we also have access to a ∆-approximate rank-r decomposition" (p.11) → the decomposition (U, V, S) is part of the input; reason: as the page says
--   - encoding: rank at most r, with r unrestricted → 1 ≤ r; reason: at r = 0 the matrix is empty, and the printed time bound can be below one step
--   - encoding: real parameters s ≥ 1 → natural numbers s ≥ 1 in input cells; reason: the integer bank cannot read a real; the statement at the floor of a real parameter implies it at that parameter, up to a constant factor in the time
--   - encoding: log r → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - encoding: the exponent 1 + o(1) and the factor n^{o(1)} → functions f, g tending to 0, chosen with the program: time κ·X^{1+f(X)} and count κ·…·n^{g(n)}; reason: the definition of o(1), with the constant κ absorbing small arguments
--   - generalization: T given as a parameter of the lemma → the program does not read T, and the clauses hold for every T above the count; reason: the printed proof never uses T; instantiating T gives the printed form
--   - encoding: integer entries of [±2^{(s log r)^{O(1)}}] → a sign and an array of at most (s log(r+2))^c bits; reason: these integers do not fit a word; the printed (rs)^{O(1)}n² pays for writing them
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 4.9, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RealAPSP_Rank
import Definitions.Def_RealAPSP_Potential

namespace RealAPSP

/-- **Lemma 4.9 (Real-to-Integer Reduction for Low-Rank Reals).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.13 (PDF p.15).

Input: `n, r, s, m`, the matrices with `∆`, and a `∆`-approximate rank-`r` decomposition of the matrix numbered `m`. The program does not read the bound `T` of the page, which is quantified after the run. Output: `|𝒯|` at output cell `0`, the number `M` of integer instances at
output cell `1`, the bit length `b` at output cell `2`, the triples of `𝒯` from output cell `3`, then the integer entries (`RealAPSP.intEntry`), of size at most `2^b`. The exponents `c` are chosen before the failure exponent; `f, g` are the page's `o(1)`. -/
theorem lemma_4_9 :
    ∃ c : ℕ, ∀ a : ℕ, ∃ (P : Program) (f : ℝ → ℝ) (g : ℕ → ℝ) (κ : ℝ),
      Filter.Tendsto f Filter.atTop (nhds 0) ∧ Filter.Tendsto g Filter.atTop (nhds 0) ∧
      ∀ (n r s : ℕ), 1 ≤ n → 1 ≤ r → 1 ≤ s → ∀ Δ : ℝ, 0 ≤ Δ →
        ∀ (m : Fin 3) (A B C : Mat ℝ n) (U : Fin n → Fin r → ℝ) (V : Fin r → Fin n → ℝ)
          (S : Fin n → Fin n → Option (Fin r)), IsRankDecomp Δ (pick m A B C) r U V S →
        let X : ℝ := ((r : ℝ) * s) ^ c * (n : ℝ) ^ 2 + (n : ℝ) ^ 3 / (s : ℝ) ^ ((1 : ℝ) / 10 ^ 5)
        RunsWhp P (n + r + s + 2) (triInts [(n : ℤ), (r : ℤ), (s : ℤ), ((m : ℕ) : ℤ)] A B C ++ decompInts S)
          (triReals [Δ] A B C ++ decompReals U V) (κ * X ^ (1 + f X)) ((n : ℝ) ^ (-(a : ℝ))) (fun σ =>
            let ℓ := (σ.imem (outCell 0)).toNat
            let M := (σ.imem (outCell 1)).toNat
            let b := (σ.imem (outCell 2)).toNat
            let 𝒯 := reportedTriples n σ 3 ℓ
            let inst : ℕ → Fin 3 → Mat ℝ n := fun q mat => castMat fun x y => intEntry σ n (3 + 3 * ℓ) b q mat x y
            (b : ℝ) ≤ ((s : ℝ) * Real.log ((r : ℝ) + 2)) ^ c ∧
            (M : ℝ) ≤ κ * (s : ℝ) * (n : ℝ) ^ g n ∧
            (∀ T : ℕ, approxCount (2 * Δ) A B C ≤ T →
              𝒯.card ≤ T ∧ ∀ q < M, approxCount 0 (inst q 0) (inst q 1) (inst q 2) ≤ T) ∧
            (∀ i k j, IsApproxTri Δ A B C i k j →
              (i, k, j) ∈ 𝒯 ∨ ∃ q < M, IsApproxTri 0 (inst q 0) (inst q 1) (inst q 2) i k j) ∧
            (∀ q < M, ∀ i k j, IsNegTri (inst q 0) (inst q 1) (inst q 2) i k j →
              ∃ x, triSum A B C i k j = some x ∧ x < 2 * Δ)) := by sorry

end RealAPSP
