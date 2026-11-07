-- Prove2me | Theorems.Thm_QuarticGap_lemma_4_2
-- name    : QuarticGap.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:12.960451+00:00
-- url     : https://prove2.me/theorems/8206c2e8-37f6-460c-b3af-85f0139051f3
-- title:
--   Lemma 4.2 — $\widehat A_W^{-1}\widehat b = x_W/(2\alpha)$, and $D_W = \|x_W\|^2$ concentrates around $d_n$
-- statement:
--   Let $\lambda \in (0,1]$, $\alpha \in (0,1/(1+8\lambda)]$ be rational. For every sign matrix $W$, not only $W \in \mathcal G$,
--   $$
--   \widehat A_W^{-1}\widehat b = \frac{x_W}{2\alpha}, \qquad x_W = \begin{pmatrix} u \\ u+\lambda v \\ u+\lambda e_0+\lambda^2 y \\ \alpha u \end{pmatrix}.
--   $$
--   The squared norm $D_W = \|x_W\|^2$ satisfies $D_W \ge 1$ and
--   $$
--   D_W = d_n + (\lambda^2+\lambda^4)(\nu-1) + 2\lambda(1+\lambda^2)\omega + 2\lambda^2 v_{0^k}, \qquad d_n = 3+\alpha^2+2\lambda^2+\lambda^4+\frac{2\lambda}{\sqrt n},
--   $$
--   where $\omega = u^{\mathsf T} v$. For uniformly random $W$, $\mathbb E D_W = d_n$ and $\mathbb E|D_W-d_n| \le C_\lambda/\sqrt n$, with $C_\lambda = \sqrt2(\lambda^2+\lambda^4)+2\lambda(1+\lambda^2)+2\lambda^2$.
--
--   The third block of the solution is an affine function of the Fourier coefficients $Z_j = \sqrt n\, y_j$, which is what the classical lower bound exploits.
--
--   **Formalization Note** Lean's matrix inverse is $0$ on a singular matrix, so the first identity also says that $\widehat A_W$ is invertible.
--
--   Differences from the source:
--   - encoding: n a power of four, indices {0,1}^k → n = 4^ℓ, k = 2ℓ, √n = 2^ℓ; reason: the same values of n
--   - encoding: independent uniform signs, uniformly random f or W → the uniform distribution on the finite set of sign functions; reason: the same law
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 4.2, p.30

import Mathlib
import Definitions.Def_QuarticGap_Ahat

open QAlgorithms

namespace QuarticGap

/-- Lemma 4.2 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.30). For every `W` (not only `W ∈ G`),
`Â_W⁻¹b̂ = x_W/(2α)`, with `x_W` as in (16). `D_W = ∥x_W∥²` satisfies `D_W ≥ 1` and
`D_W = d_n + (λ² + λ⁴)(ν − 1) + 2λ(1 + λ²)ω + 2λ²v_{0^k}`. For uniformly random `W`, `𝔼D_W = d_n` and
`𝔼|D_W − d_n| ≤ C_λ/√n`.

**Formalization Note** `(Ahat lam α W)⁻¹` is Mathlib's matrix inverse, which is `0` on a singular
matrix; the first clause therefore also says that `Â_W` is invertible, as it is unipotent up to the
diagonal `α`, `1`. -/
theorem lemma_4_2 {ℓ : ℕ} (lam α : ℚ) (hlam : 0 < lam ∧ lam ≤ 1)
    (hα : 0 < α ∧ α ≤ 1 / (1 + 8 * lam)) :
    (∀ W : SignMat ℓ,
      (Ahat lam α W)⁻¹.mulVec (bhat ℓ) = (fun i => xW lam α W i / (2 * (α : ℝ))) ∧
      1 ≤ DW lam α W ∧
      DW lam α W = dn ℓ lam α + ((lam : ℝ) ^ 2 + (lam : ℝ) ^ 4) * (nu W - 1) +
        2 * lam * (1 + (lam : ℝ) ^ 2) * omega W + 2 * (lam : ℝ) ^ 2 * vVec W (zeros _)) ∧
    uAvg (fun W : SignMat ℓ => DW lam α W) = dn ℓ lam α ∧
    uAvg (fun W : SignMat ℓ => |DW lam α W - dn ℓ lam α|) ≤ Clam lam / 2 ^ ℓ := by sorry

end QuarticGap
