-- Prove2me | Theorems.Thm_QuarticGap_lemma_4_1
-- name    : QuarticGap.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:59.400701+00:00
-- url     : https://prove2.me/theorems/eca092c3-2000-47b4-976c-7e1509d62f59
-- title:
--   Lemma 4.1 — $\|\widehat A_W\| = 1$, $\kappa(\widehat A_W) \le (1+8\lambda+8\lambda^2)/\alpha$, $\rho(\widehat A_W)^2 = n(1+\alpha^2(3+2\lambda^2))$
-- statement:
--   Let $\lambda \in (0,1]$ and $\alpha \in (0,1/(1+8\lambda)]$ be rational and $n = 4^\ell$. For every $W \in \mathcal G$,
--   $$
--   \|\widehat A_W\| = 1, \qquad \kappa(\widehat A_W) \le \frac{1+8\lambda+8\lambda^2}{\alpha}, \qquad \rho(\widehat A_W)^2 = n\bigl(1+\alpha^2(3+2\lambda^2)\bigr).
--   $$
--   For $\alpha = 1/(1+8\lambda)$, the condition number is at most $(1+8\lambda)(1+8\lambda+8\lambda^2) \le 1+152\lambda$. The entries that depend on $W$ are $-\alpha\lambda W_{ab}/\sqrt n$, in row $n+a$ and column $b$, so the family has known magnitudes in the sense of Lemma 2.7, with $f(a,b) = W_{ab}$.
--
--   This normalizes the family: the condition number stays constant while $\rho^2$ grows like $n$, which turns the bounds in $n$ into bounds in $\rho$.
--
--   **Formalization Note** Row $n+a$ is block $1$, position $a$, and column $b$ is block $0$, position $b$.
--
--   Differences from the source:
--   - encoding: n a power of four, indices {0,1}^k → n = 4^ℓ, k = 2ℓ, √n = 2^ℓ; reason: the same values of n
--   - encoding: the family satisfies the hypotheses of Lemma 2.7, including a fixed reversible circuit for (i, j) ↦ σ_ij → IsKnownMagnitudeFamily, the hypotheses of the Lean Lemma 2.7; reason: every map on bit strings is computed by some fixed reversible circuit, and here σ for row n + a, column b is (a, b), a relabelling of wires
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 4.1, p.29

import Mathlib
import Definitions.Def_QuarticGap_Ahat

open QAlgorithms

namespace QuarticGap

/-- Lemma 4.1 (Chakrabarti, Herman, Kim, Ozgul, arXiv:2610.42069 (file sha256 9f68aaf9…), p.29).
For every `W ∈ G`: `∥Â_W∥ = 1`, `κ(Â_W) ≤ (1 + 8λ + 8λ²)/α`, `ρ(Â_W)² = n(1 + α²(3 + 2λ²))`. For
`α = 1/(1 + 8λ)`, `κ ≤ (1 + 8λ)(1 + 8λ + 8λ²) ≤ 1 + 152λ`. The entries that depend on `W` are
`−αλW_ab/√n`, in row `n + a` and column `b`, so the family satisfies the hypotheses of Lemma 2.7 with
`f(a, b) = W_ab`.

**Formalization Note** `n = 4^ℓ`, `√n = 2^ℓ`. Row `n + a` is block `1`, position `a`; column `b` is
block `0`, position `b`. `λ, α` carry the standing assumptions of §4.1. -/
theorem lemma_4_1 {ℓ : ℕ} (lam α : ℚ) (hlam : 0 < lam ∧ lam ≤ 1)
    (hα : 0 < α ∧ α ≤ 1 / (1 + 8 * lam)) :
    (∀ W ∈ G ℓ,
      specNorm (Ahat lam α W) = 1 ∧
      specNorm (Ahat lam α W) * specNorm (Ahat lam α W)⁻¹ ≤
        (1 + 8 * (lam : ℝ) + 8 * (lam : ℝ) ^ 2) / α ∧
      rho (Ahat lam α W) ^ 2 = 4 ^ ℓ * (1 + (α : ℝ) ^ 2 * (3 + 2 * (lam : ℝ) ^ 2)) ∧
      (α = 1 / (1 + 8 * lam) →
        specNorm (Ahat lam α W) * specNorm (Ahat lam α W)⁻¹ ≤
          (1 + 8 * (lam : ℝ)) * (1 + 8 * (lam : ℝ) + 8 * (lam : ℝ) ^ 2))) ∧
    (1 + 8 * (lam : ℝ)) * (1 + 8 * (lam : ℝ) + 8 * (lam : ℝ) ^ 2) ≤ 1 + 152 * lam ∧
    (∀ (W : SignMat ℓ) (i j : Idx ℓ), blk i = 1 → blk j = 0 →
      Ahat lam α W i j = -(α * lam * sgn (W (dat i) (dat j))) / 2 ^ ℓ) ∧
    (∀ (W W' : SignMat ℓ) (i j : Idx ℓ), ¬ (blk i = 1 ∧ blk j = 0) →
      Ahat lam α W i j = Ahat lam α W' i j) ∧
    IsKnownMagnitudeFamily (fun f : Qubits (2 * ℓ + 2 * ℓ) → ℤˣ => Ahat lam α (unflat f)) := by sorry

end QuarticGap
