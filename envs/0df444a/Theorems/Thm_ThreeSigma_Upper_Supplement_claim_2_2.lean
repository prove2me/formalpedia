-- Prove2me | Theorems.Thm_ThreeSigma_Upper_Supplement_claim_2_2
-- name    : ThreeSigma.Upper.Supplement.claim_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:17:22.953613+00:00
-- url     : https://prove2.me/theorems/7e32c9f8-03d6-4f11-901c-c91ea9d46cc3
-- title:
--   Claim (§2.2) — $\|H\varepsilon\|_1$ is rarely above $0.99\,n^{3/2}$
-- statement:
--   Let $\delta=2^{-22}$, let $n\ge2^{50}$ be a power of two and let $H_0\in\{-1,1\}^{n\times n}$ be a Hadamard matrix ($H_0^\top H_0=nI_n$). Fix any set $S$ of $\delta n$ columns and let $H$ be the $n\times(1-\delta)n$ matrix formed by the columns of $H_0$ outside $S$. Let $\varepsilon$ be uniform on $\{-1,1\}^{(1-\delta)n}$. Then
--   $$\mathbb P_\varepsilon\big[\|H\varepsilon\|_1>0.99\,n^{3/2}\big]<2^{-n/310}.$$
--
--   This is the step of the proof of Theorem 1.1 that bounds the number of sign vectors $u$ for which only the weaker bound of Lemma 2.3(a) is available.
--
--   **Formalization Note** The hypotheses on $n$, $H_0$ and $S$ are the context of Theorem 1.1, in which the Claim appears; they are stated explicitly. The coordinates of $\varepsilon$ are indexed by the columns outside $S$, and $\|H\varepsilon\|_1=\sum_i\big|\sum_{j\notin S}(H_0)_{ij}\varepsilon_j\big|$.
--
--   Differences from the source:
--   - encoding: ε uniform on {−1,1}^m; ℙ and 𝔼 over ε → uniformProb / uniformAvg: the fraction (average) over the 2^m vectors of signVectors; reason: the uniform law on a finite cube is the normalized count; same values
--   - encoding: the context of Theorem 1.1 (n ≥ 2^50 a power of two, H0 Hadamard, S any set of δn columns, H the other columns) → explicit binders hn, hpow, IsHadamard H0, (S.card : ℝ) = δ·n; ε indexed by {j // j ∉ S}; reason: the Claim is stated inside the proof of Theorem 1.1; its hypotheses made explicit
--   - encoding: ‖Hε‖₁ > 0.99n^{3/2} → 99/100 · n^{3/2} < ∑ i, |∑ j ∉ S, H0 i j · ε j|; reason: definition of the ℓ1 norm of Hε ∈ ℝ^n, with H the columns of H0 outside S
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Claim (§2.2), p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf (SHA-256 3be06ff7fede4a6b259a8de8615176523f985a50a464328e2179c71e52153940)

import Definitions.Def_ThreeSigma_Upper_Supplement_Model

namespace ThreeSigma.Upper.Supplement

/-- Claim in the proof of Theorem 1.1 (§2.2, p. 4), with Theorem 1.1's context explicit:
n ≥ 2^50 a power of two, H0 an n×n Hadamard matrix, S any set of δn columns, and H the
n×(1−δ)n matrix of the columns of H0 outside S. For ε uniform on {−1,1}^{(1−δ)n}
(indexed by the columns outside S), ℙ[‖Hε‖₁ > 0.99 n^{3/2}] < 2^{−n/310}. -/
theorem claim_2_2 (n : ℕ) (hn : 2 ^ 50 ≤ n) (hpow : ∃ m : ℕ, n = 2 ^ m)
    (H0 : Matrix (Fin n) (Fin n) ℝ) (hH0 : IsHadamard H0)
    (S : Finset (Fin n)) (hS : (S.card : ℝ) = delta * n) :
    uniformProb (fun ε : {j // j ∉ S} → ℝ =>
        99 / 100 * (n : ℝ) ^ ((3 : ℝ) / 2) < ∑ i, |∑ j : {j // j ∉ S}, H0 i j * ε j|) <
      (2 : ℝ) ^ (-(n : ℝ) / 310) := by sorry

end ThreeSigma.Upper.Supplement
