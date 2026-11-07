-- Prove2me | Theorems.Thm_SYKEdge_theorem_5_2
-- name    : SYKEdge.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:38.950193+00:00
-- url     : https://prove2.me/theorems/66c17e2b-a842-4c8b-a4df-7ec5e2a81f22
-- title:
--   Theorem 5.2 — dense SYK upper bound $\mathbb E\|H\|_{op}\le\sqrt{2/\alpha}+O(1)$
-- statement:
--   Let $n\ge k\ge2$ be even integers with $\alpha=k^2/n<1/16$, and let $H=\binom nk^{-1/2}\sum_{S\in\binom{[n]}k}g_S\Gamma_S$ be the dense SYK Hamiltonian with i.i.d. $N(0,1)$ disorder, on Majorana operators of dimension $2^{n/2}$. Then
--   $$\mathbb E\|H\|_{op}\le\sqrt{2/\alpha}+O(1).$$
--   In particular, if $\alpha\le o_n(1)$ then $\mathbb E\|H\|_{op}\le(1+o(1))\sqrt{2/\alpha}$.
--
--   Since $\sqrt{2/\alpha}=\sqrt{2n}/k$, this is the upper half of the spectral edge (Theorem 1.1).
--
--   **Formalization Note** The "in particular" clause is stated uniformly: for every $\eta>0$ there is $c>0$ such that $\alpha\le c$ forces $\mathbb E\|H\|_{op}\le(1+\eta)\sqrt{2/\alpha}$.
--
--   Differences from the source:
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - encoding: O(1) in E‖H‖_op ⩽ √(2/α) + O(1) → one absolute constant C > 0 quantified before n, k, the representation and the family; reason: the paper's O(1) are absolute constants (footnote 20, p.36)
--   - reading: if α ⩽ o_n(1) then E‖H‖_op ⩽ (1 + o(1))√(2/α) → ∀ η > 0 ∃ c > 0 such that α ⩽ c implies E‖H‖_op ⩽ (1 + η)√(2/α), uniformly in n, k and the family; reason: this is the sequence-free content of the asymptotic statement and is equivalent to it for every sequence with α → 0
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Theorem 5.2, p.35

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
open Matrix MeasureTheory

namespace SYKEdge

/-- **Theorem 5.2** (Operator Norm of the Dense SYK: Upper Bound), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.35.

Let `n ⩾ k ⩾ 2` be even integers and `α := k²/n < 1/16`. For the dense SYK Hamiltonian
`H = (n choose k)^{−1/2} Σ_S g_S Γ_S`, `E‖H‖_op ⩽ √(2/α) + O(1)`. In particular, if `α ⩽ o_n(1)` then
`E‖H‖_op ⩽ (1 + o(1))·√(2/α)`.

**Formalization Note.** `O(1)` is one absolute constant `C > 0` chosen before `n, k` and the
representation (footnote 20). The "In particular" clause is stated uniformly: for every `η > 0` there
is `c > 0` such that `α ⩽ c` forces `E‖H‖_op ⩽ (1 + η)√(2/α)`. Representations: any Majorana family
of dimension `2^{n/2}`. -/
theorem theorem_5_2 :
    (∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, Even n → Even k → 2 ≤ k → k ≤ n → (k : ℝ) ^ 2 / n < 1 / 16 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
      ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
        ∫ g, opNorm (sykDense γ g) ∂stdGauss (KSet n k) ≤
          Real.sqrt (2 / ((k : ℝ) ^ 2 / n)) + C) ∧
    (∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧
      ∀ n k : ℕ, Even n → Even k → 2 ≤ k → k ≤ n → (k : ℝ) ^ 2 / n < 1 / 16 →
        (k : ℝ) ^ 2 / n ≤ c →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
      ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
        ∫ g, opNorm (sykDense γ g) ∂stdGauss (KSet n k) ≤
          (1 + η) * Real.sqrt (2 / ((k : ℝ) ^ 2 / n))) := by sorry

end SYKEdge
