-- Prove2me | Theorems.Thm_SYKEdge_theorem_5_3
-- name    : SYKEdge.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:35.308597+00:00
-- url     : https://prove2.me/theorems/c821f195-f48f-4120-a220-c3c860d95c74
-- title:
--   Theorem 5.3 — dense SYK lower bound $\mathbb E\|H\|_{op}\ge\frac{\sqrt{2n}}k\big(1-O(1)\max\{k^{-1/2},k^4/n^2\}\big)$, also for $\lambda_{\max}$
-- statement:
--   Let $n\ge k\ge2$ be even integers with $\alpha=k^2/n<1/16$, and let $H$ be the dense SYK Hamiltonian on Majorana operators of dimension $2^{n/2}$. Then
--   $$\mathbb E\|H\|_{op}\ \ge\ \sqrt{\frac2\alpha}\Big(1-O(1)\max\{k^{-1/2},\alpha^2\}\Big)=\frac{\sqrt{2n}}k\Big(1-O(1)\max\Big\{k^{-1/2},\frac{k^4}{n^2}\Big\}\Big),$$
--   and the same lower bound holds for $\mathbb E\lambda_{\max}(H)$, the expected ground-state energy of $-H$.
--
--   With Theorem 5.2 this pins the spectral edge to $(1\pm o(1))\sqrt{2n}/k$ when $k\to\infty$ and $k=o(\sqrt n)$.
--
--   **Formalization Note** Stated in the second (equal) form.
--
--   Differences from the source:
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - encoding: O(1) in the lower bound → one absolute constant C > 0 quantified before n, k, the representation and the family; reason: the paper's O(1) are absolute constants (footnote 20, p.36)
--   - generalization: the lower bound stated for ‖H‖_op → the lower bound stated for ‖H‖_op and, as a second conjunct, for λ_max(H); reason: Remark 1.2(1) and footnote 4 (pp.2–3) assert that the argument applies to λ_max; dropping the conjunct gives the printed statement
--   - encoding: the chain √(2/α)·(1 − O(1)·max{k^{−1/2}, α²}) = (√(2n)/k)·(1 − O(1)·max{k^{−1/2}, k⁴/n²}) → only the second form, (√(2n)/k)·(1 − C·max{k^{−1/2}, k⁴/n²}); reason: √(2/α) = √(2n)/k and α² = k⁴/n² are arithmetic for α = k²/n, so the two forms are the same bound
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Theorem 5.3, p.36; Remark 1.2(1) and footnote 4, pp.2–3

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
open Matrix MeasureTheory

namespace SYKEdge

/-- **Theorem 5.3** (Operator Norm of the Dense SYK: Lower Bound), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.36; the `λ_max` form from
Remark 1.2(1) and footnote 4, pp.2–3.

Let `n ⩾ k ⩾ 2` be even integers and `α := k²/n < 1/16`. For the dense SYK Hamiltonian,
`E‖H‖_op ⩾ √(2/α)·(1 − O(1)·max{k^{−1/2}, α²}) = (√(2n)/k)·(1 − O(1)·max{k^{−1/2}, k⁴/n²})`, and the
same lower bound holds for `E λ_max(H)`.

**Formalization Note.** Stated in the second (equal) form, `√(2/α) = √(2n)/k`, `α² = k⁴/n²`. `O(1)` is
one absolute `C > 0` chosen before `n, k` and the representation. Majorana families of dimension
`2^{n/2}`. -/
theorem theorem_5_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, Even n → Even k → 2 ≤ k → k ≤ n → (k : ℝ) ^ 2 / n < 1 / 16 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
      ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
        Real.sqrt (2 * n) / k *
            (1 - C * max ((k : ℝ) ^ (-(1 / 2 : ℝ))) ((k : ℝ) ^ 4 / (n : ℝ) ^ 2))
          ≤ ∫ g, opNorm (sykDense γ g) ∂stdGauss (KSet n k) ∧
        Real.sqrt (2 * n) / k *
            (1 - C * max ((k : ℝ) ^ (-(1 / 2 : ℝ))) ((k : ℝ) ^ 4 / (n : ℝ) ^ 2))
          ≤ ∫ g, lamMax (sykDense γ g) ∂stdGauss (KSet n k) := by sorry

end SYKEdge
