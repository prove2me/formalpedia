-- Prove2me | Theorems.Thm_ThreeSigma_Upper_Supplement_lemma_2_2
-- name    : ThreeSigma.Upper.Supplement.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:16:18.497426+00:00
-- url     : https://prove2.me/theorems/ff8743a3-8204-43b5-9dda-d12bb2e4a9b7
-- title:
--   Lemma 2.2 — four estimates for a sum of random signs
-- statement:
--   For $k\in\mathbb N$ let $S_k=\varepsilon_1+\dots+\varepsilon_k$ be the sum of $k$ independent uniform random signs, and let $\delta=2^{-22}$. Let $k\ge2$ be even. Then:
--   1. $\mathbb E[|S_k|]\le 0.8\sqrt k$.
--   2. (Hoeffding's lemma) For every $t\in\mathbb R$, $\mathbb E[\exp(tS_k/\sqrt k)]\le e^{t^2/2}$.
--   3. For every $t\in\mathbb R$, $\mathbb P[S_k\le t\sqrt k-1]\le\tfrac12\exp\!\big(\sqrt{2/\pi}\,t\big)$.
--   4. If $u\ge0$ and in addition $k\ge2^{24}$, then
--   $$\mathbb P\left[u+\sqrt{\frac{\delta}{k}}\,S_k\le1+\delta\right]\le\frac12\exp\left(4\sqrt\delta+\frac{1-u^2}{\sqrt{2\pi\delta}}\right).$$
--
--   Part 1 is used in the Claim of §2.2 and part 4 in Lemma 2.3; parts 2 and 3 are the ingredients of part 4. The paper proves all four in Appendix A.
--
--   **Formalization Note** $S_k$ is the sum of the coordinates of a uniform sign vector in $\{-1,1\}^k$; probabilities and expectations are normalized counts over the $2^k$ sign vectors.
--
--   Differences from the source:
--   - encoding: S_k, the sum of k independent uniform random signs → ∑ j, ε j for ε uniform on signVectors (Fin k), via uniformAvg / uniformProb; reason: the uniform law on {−1,1}^k gives k independent fair signs; same distribution of S_k
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Lemma 2.2, p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf (SHA-256 3be06ff7fede4a6b259a8de8615176523f985a50a464328e2179c71e52153940)

import Definitions.Def_ThreeSigma_Upper_Supplement_Model

namespace ThreeSigma.Upper.Supplement

/-- Lemma 2.2, p. 3 (proof Appendix A, pp. 10–13). S_k = ε_1 + ⋯ + ε_k for ε uniform on
{−1,1}^k; k ≥ 2 even. All four parts (a)–(d); δ = 2^{-22}. -/
theorem lemma_2_2 (k : ℕ) (hk : 2 ≤ k) (hk_even : Even k) :
    -- (a) 𝔼|S_k| ≤ 0.8 √k
    uniformAvg (fun ε : Fin k → ℝ => |∑ j, ε j|) ≤ 4 / 5 * Real.sqrt k ∧
    -- (b) Hoeffding's lemma: 𝔼[exp(t S_k / √k)] ≤ e^{t²/2} for every real t
    (∀ t : ℝ, uniformAvg (fun ε : Fin k → ℝ => Real.exp (t * (∑ j, ε j) / Real.sqrt k)) ≤
      Real.exp (t ^ 2 / 2)) ∧
    -- (c) ℙ[S_k ≤ t√k − 1] ≤ ½ exp(√(2/π) t) for every real t
    (∀ t : ℝ, uniformProb (fun ε : Fin k → ℝ => ∑ j, ε j ≤ t * Real.sqrt k - 1) ≤
      1 / 2 * Real.exp (Real.sqrt (2 / Real.pi) * t)) ∧
    -- (d) for u ≥ 0 and k ≥ 2^24:
    --     ℙ[u + √(δ/k) S_k ≤ 1 + δ] ≤ ½ exp(4√δ + (1 − u²)/√(2πδ))
    (∀ u : ℝ, 0 ≤ u → 2 ^ 24 ≤ k →
      uniformProb (fun ε : Fin k → ℝ =>
          u + Real.sqrt (delta / k) * (∑ j, ε j) ≤ 1 + delta) ≤
        1 / 2 * Real.exp (4 * Real.sqrt delta +
          (1 - u ^ 2) / Real.sqrt (2 * Real.pi * delta))) := by sorry

end ThreeSigma.Upper.Supplement
