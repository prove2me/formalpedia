-- Prove2me | Theorems.Thm_ThreeSigma_Upper_Supplement_theorem_1_1
-- name    : ThreeSigma.Upper.Supplement.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:17:48.62665+00:00
-- url     : https://prove2.me/theorems/9959745e-3c2f-4c71-9041-6a74b07613aa
-- title:
--   Theorem 1.1 — a Hadamard matrix with $2^{-22}$ of its columns randomized has discrepancy above $(1+\delta)\sqrt n$; $\limsup D_n^\pm>1.0000002$
-- statement:
--   Let $\delta=2^{-22}$, let $n\ge2^{50}$ be a power of two and let $H_0\in\{-1,1\}^{n\times n}$ be a Hadamard matrix. Fix any set of $\delta n$ columns and let $A:=[H\mid R]$ be obtained by replacing those columns with a matrix $R$ of independent uniform random signs. Then
--   $$\mathbb P\big[\operatorname{disc}(A)>(1+\delta)\sqrt n\big]\ge1-2^{-n/20000},$$
--   where $\operatorname{disc}(A)=\min_{x\in\{-1,1\}^n}\|Ax\|_\infty$. In particular,
--   $$\limsup_{n\to\infty}D_n^\pm>1.0000002,\qquad D_n^\pm=\max_{A\in\{-1,1\}^{n\times n}}\frac{\operatorname{disc}(A)}{\sqrt n}.$$
--
--   This is the paper's lower bound, which proves Bandeira's conjecture $\limsup_n D_n^\pm>1$ and improves the bound $D_n^\pm\ge1$ of Olson and Spencer given by Hadamard matrices. It is a companion of the mission's goal (Theorem 1.2, the upper bound) and not a step in its proof.
--
--   **Formalization Note** The probability is the fraction of the sign matrices $R\in\{-1,1\}^{n\times S}$ for which the event holds. The replaced columns keep their positions. The lim sup clause is stated as: there is $c>1.0000002$ with $D_n^\pm\ge c$ for infinitely many $n$, which is equivalent to $\limsup_n D_n^\pm>1.0000002$ for a real sequence.
--
--   Differences from the source:
--   - encoding: R a matrix of independent random signs; ℙ over R → uniformProb over R ∈ signVectors (Fin n × S); reason: the uniform law on a finite cube is the normalized count; same values
--   - encoding: A := [H | R], the replaced columns moved to the right → replaceCols H0 S R, the replaced columns kept in place; reason: disc(A) is invariant under permuting columns (and permuting the coordinates of x)
--   - encoding: the set of δn columns → S : Finset (Fin n) with (S.card : ℝ) = δ·n; reason: same sets of columns
--   - encoding: lim sup_{n→∞} D_n^± > 1.0000002 → ∃ c > 1.0000002, ∃ᶠ n in atTop, c ≤ D_n^±; reason: equivalent for every real sequence; avoids Real limsup junk values
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Theorem 1.1, p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf (SHA-256 3be06ff7fede4a6b259a8de8615176523f985a50a464328e2179c71e52153940)

import Definitions.Def_ThreeSigma_Upper_Supplement_Model

namespace ThreeSigma.Upper.Supplement

/-- Theorem 1.1, p. 2 (proof §2.2, p. 4). For every power of two n ≥ 2^50, every Hadamard
H0 of order n and every set S of δn columns (δ = 2^{-22}), let A := [H | R] replace the
columns in S by independent uniform random signs R. Then
ℙ_R[disc(A) > (1 + δ)√n] ≥ 1 − 2^{−n/20000}.
In particular lim sup_{n→∞} D_n^± > 1.0000002, written as: some c > 1.0000002 has
c ≤ D_n^± for infinitely many n (equivalent to the lim sup statement). -/
theorem theorem_1_1 :
    (∀ (n : ℕ), 2 ^ 50 ≤ n → (∃ m : ℕ, n = 2 ^ m) →
      ∀ (H0 : Matrix (Fin n) (Fin n) ℝ), IsHadamard H0 →
      ∀ (S : Finset (Fin n)), (S.card : ℝ) = delta * n →
        1 - (2 : ℝ) ^ (-(n : ℝ) / 20000) ≤
          uniformProb (fun R : Fin n × {j // j ∈ S} → ℝ =>
            (1 + delta) * Real.sqrt n < disc (replaceCols H0 S R))) ∧
    (∃ c : ℝ, (10000002 : ℝ) / 10000000 < c ∧ ∃ᶠ n in Filter.atTop, c ≤ Dpm n) := by sorry

end ThreeSigma.Upper.Supplement
