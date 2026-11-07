-- Prove2me | Theorems.Thm_SYKEdge_theorem_1_1
-- name    : SYKEdge.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:52.969847+00:00
-- url     : https://prove2.me/theorems/aef59593-784f-453b-9de5-aec2a0197c14
-- title:
--   Theorem 1.1 — spectral edge of SYK: $\frac{\sqrt{2n}}k\big(1-O(1)\max\{k^{-1/2},\frac{k^4}{n^2}\}\big)\le\mathbb E\|H_{SYK}\|_{op}\le\frac{\sqrt{2n}}k+O(1)$
-- statement:
--   Let $n\ge k\ge2$ be even integers with $k^2/n<1/16$, and let
--   $$H_{SYK}=\binom nk^{-1/2}\sum_{S\in\binom{[n]}k}g_S\Gamma_S$$
--   be the dense SYK Hamiltonian, with i.i.d. $N(0,1)$ disorder $g_S$ and Majorana monomials $\Gamma_S$ built from any family of $n$ Majorana operators of dimension $2^{n/2}$. Then
--   $$\frac{\sqrt{2n}}k\Big(1-O(1)\cdot\max\Big\{k^{-1/2},\frac{k^4}{n^2}\Big\}\Big)\ \le\ \mathbb E_g\|H_{SYK}\|_{op}\ \le\ \frac{\sqrt{2n}}k+O(1),$$
--   and the lower bound holds for $\mathbb E_g\lambda_{\max}(H_{SYK})$ as well. In particular, if $\omega_n(1)\le k\le o(\sqrt n)$, then
--   $$\mathbb E_g\lambda_{\max}(H_{SYK}),\ \mathbb E_g\|H_{SYK}\|_{op}=(1-o_n(1))\cdot\frac{\sqrt{2n}}k .$$
--
--   This identifies the spectral edge of the SYK model up to a factor $1\pm o(1)$, closing the factor-$k$ gap between the earlier $O(\sqrt n)$ upper and $\Omega(\sqrt n/k)$ lower bounds.
--
--   **Formalization Note** Every $O(1)$ is one absolute constant $C>0$ chosen before $n$, $k$ and the Majorana family. $\mathbb E_g$ is the integral against the product of $N(0,1)$ laws indexed by the $k$-subsets. The "in particular" clause is stated uniformly: for every $\eta>0$ there are $K_0$ and $c>0$ such that $k\ge K_0$ and $k^2/n\le c$ put both expectations within a factor $1\pm\eta$ of $\sqrt{2n}/k$.
--
--   Differences from the source:
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - encoding: O(1) in both bounds → one absolute constant C > 0 quantified before n, k, the representation and the family; reason: the paper's O(1) are absolute constants (footnote 20, p.36)
--   - generalization: the lower bound stated for ‖H‖_op → the lower bound stated for ‖H‖_op and, as a second conjunct, for λ_max(H); reason: Remark 1.2(1) and footnote 4 (pp.2–3) assert that the argument applies to λ_max; dropping the conjunct gives the printed statement
--   - reading: if ω_n(1) ⩽ k ⩽ o(√n), then E λ_max(H_SYK), E‖H_SYK‖_op = (1 − o_n(1))·√(2n)/k → ∀ η > 0 ∃ K₀ ∃ c > 0: k ⩾ K₀ and k²/n ⩽ c imply |E λ_max/(√(2n)/k) − 1| ⩽ η and |E‖H‖_op/(√(2n)/k) − 1| ⩽ η, uniformly in the family; reason: the sequence-free content of the asymptotic clause; equivalent to it along every sequence with k → ∞ and k/√n → 0
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Theorem 1.1, p.2; Remark 1.2(1) and footnote 4, pp.2–3; footnote 20, p.36

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
open Matrix MeasureTheory

namespace SYKEdge

/-- **Theorem 1.1** (Spectral Edge of SYK), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.2 (PDF p.2).

Let `n ⩾ k ⩾ 2` be even integers with `k²/n < 1/16`, and let `H_SYK` be the dense SYK Hamiltonian (1)
on any family of Majorana operators of dimension `N = 2^{n/2}`. Then
`(√(2n)/k)(1 − O(1)·max{k^{−1/2}, k⁴/n²}) ⩽ E_g ‖H_SYK‖_op ⩽ √(2n)/k + O(1)`; the lower bound also holds
for `E_g λ_max(H_SYK)` (Remark 1.2(1), footnote 4); and in particular, if `ω_n(1) ⩽ k ⩽ o(√n)`, both
`E_g λ_max(H_SYK)` and `E_g ‖H_SYK‖_op` equal `(1 − o_n(1))·√(2n)/k`.

**Formalization Note.**
* Every `O(1)` is one absolute constant `C > 0`, chosen before `n`, `k`, the representation and the
  family (footnote 20, p.36).
* The representation is any `γ : Fin n → Matrix ι ι ℂ` with `card ι = 2^{n/2}` satisfying the
  Majorana relations (p.15, footnote 14).
* `E_g` is the integral against i.i.d. `N(0,1)` disorder `g_S`, one per `k`-subset `S`.
* The "In particular" clause is stated in its uniform, sequence-free form: for every `η > 0` there
  are `K₀` and `c > 0` such that `k ⩾ K₀` and `k²/n ⩽ c` force both expectations to lie within a
  factor `1 ± η` of `√(2n)/k`. -/
theorem theorem_1_1 :
    (∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, Even n → Even k → 2 ≤ k → k ≤ n → (k : ℝ) ^ 2 / n < 1 / 16 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
      ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
        Real.sqrt (2 * n) / k *
            (1 - C * max ((k : ℝ) ^ (-(1 / 2 : ℝ))) ((k : ℝ) ^ 4 / (n : ℝ) ^ 2))
          ≤ ∫ g, lamMax (sykDense γ g) ∂stdGauss (KSet n k) ∧
        Real.sqrt (2 * n) / k *
            (1 - C * max ((k : ℝ) ^ (-(1 / 2 : ℝ))) ((k : ℝ) ^ 4 / (n : ℝ) ^ 2))
          ≤ ∫ g, opNorm (sykDense γ g) ∂stdGauss (KSet n k) ∧
        ∫ g, opNorm (sykDense γ g) ∂stdGauss (KSet n k) ≤ Real.sqrt (2 * n) / k + C) ∧
    (∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n k : ℕ, Even n → Even k → 2 ≤ k → k ≤ n → K₀ ≤ k → (k : ℝ) ^ 2 / n ≤ c →
        (k : ℝ) ^ 2 / n < 1 / 16 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
      ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
        |(∫ g, lamMax (sykDense γ g) ∂stdGauss (KSet n k)) / (Real.sqrt (2 * n) / k) - 1| ≤ η ∧
        |(∫ g, opNorm (sykDense γ g) ∂stdGauss (KSet n k)) / (Real.sqrt (2 * n) / k) - 1| ≤ η) := by sorry

end SYKEdge
