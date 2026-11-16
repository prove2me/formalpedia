-- Prove2me | Theorems.Thm_ThreeSigma_Upper_Supplement_lemma_2_3
-- name    : ThreeSigma.Upper.Supplement.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:16:51.293456+00:00
-- url     : https://prove2.me/theorems/87b62ae2-1c5e-49ff-a4c2-84fc0d9ca644
-- title:
--   Lemma 2.3 — binomial noise rarely keeps a vector of norm $\sqrt{1-\delta}\,n$ inside the $(1+\delta)\sqrt n$ box
-- statement:
--   Let $\delta=2^{-22}$, let $n\ge2^{50}$ be a power of two, and let $Y\in\mathbb R^n$ be a random vector whose coordinates are independent and distributed as $S_{\delta n}$, the sum of $\delta n$ independent uniform random signs. Then for every $z\in\mathbb R^n$ with $\|z\|_2^2=(1-\delta)n^2$:
--   1. $$\mathbb P\big[\|z+Y\|_\infty\le(1+\delta)\sqrt n\big]\le 2^{-n}\,2^{n/320}.$$
--   2. If in addition $\|z\|_1\le0.99\,n^{3/2}$, the same probability is at most $2^{-3n}$.
--
--   Both parts enter the union bound in the proof of Theorem 1.1, where $z=Hu$ for a fixed sign vector $u$ and $Y=Rv$. The paper proves them in Appendix B from Lemma 2.2(d).
--
--   **Formalization Note** $Y_i=\sum_{j<k}R_{ij}$ for $R$ uniform on $\{-1,1\}^{n\times k}$, where $k$ is the natural number with $k=\delta n$ (an integer because $n\ge2^{50}$ is a power of two). The event $\|z+Y\|_\infty\le(1+\delta)\sqrt n$ is written coordinatewise.
--
--   Differences from the source:
--   - encoding: Y with i.i.d. coordinates distributed as S_{δn} → Y_i = ∑_{j<k} R(i,j) with R uniform on signVectors (Fin n × Fin k) and a natural k with (k : ℝ) = δ·n; reason: rows of a uniform sign matrix are independent, each sum distributed as S_k; k = δn is the source's integer
--   - encoding: ‖z + Y‖∞ ≤ (1+δ)√n, ‖z‖₂², ‖z‖₁ → ∀ i, |z i + Y i| ≤ (1+δ)√n; ∑ z_i²; ∑ |z_i|; reason: definitions of the norms on ℝ^n
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Lemma 2.3, p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf (SHA-256 3be06ff7fede4a6b259a8de8615176523f985a50a464328e2179c71e52153940)

import Definitions.Def_ThreeSigma_Upper_Supplement_Model

namespace ThreeSigma.Upper.Supplement

/-- Lemma 2.3, p. 3 (proof Appendix B, p. 13). n ≥ 2^50 a power of two, k = δn, and
Y_i = ∑_{j<k} R_{ij} for a uniform sign matrix R ∈ {−1,1}^{n×k}, so the coordinates of Y
are i.i.d. copies of S_{δn}. For every z with ‖z‖₂² = (1 − δ)n²:
(a) ℙ[‖z + Y‖∞ ≤ (1 + δ)√n] ≤ 2^{−n} 2^{n/320};
(b) if also ‖z‖₁ ≤ 0.99 n^{3/2}, the same probability is ≤ 2^{−3n}. -/
theorem lemma_2_3 (n : ℕ) (hn : 2 ^ 50 ≤ n) (hpow : ∃ m : ℕ, n = 2 ^ m)
    (k : ℕ) (hk : (k : ℝ) = delta * n)
    (z : Fin n → ℝ) (hz : ∑ i, z i ^ 2 = (1 - delta) * (n : ℝ) ^ 2) :
    uniformProb (fun R : Fin n × Fin k → ℝ =>
        ∀ i, |z i + ∑ j, R (i, j)| ≤ (1 + delta) * Real.sqrt n) ≤
      (2 : ℝ) ^ (-(n : ℝ)) * (2 : ℝ) ^ ((n : ℝ) / 320) ∧
    (∑ i, |z i| ≤ 99 / 100 * (n : ℝ) ^ ((3 : ℝ) / 2) →
      uniformProb (fun R : Fin n × Fin k → ℝ =>
          ∀ i, |z i + ∑ j, R (i, j)| ≤ (1 + delta) * Real.sqrt n) ≤
        (2 : ℝ) ^ (-(3 * n : ℝ))) := by sorry

end ThreeSigma.Upper.Supplement
