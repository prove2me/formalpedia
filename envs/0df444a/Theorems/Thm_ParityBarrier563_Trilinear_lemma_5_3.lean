-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_lemma_5_3
-- name    : ParityBarrier563.Trilinear.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:48.221389+00:00
-- url     : https://prove2.me/theorems/df1796ed-64c1-4eba-9a52-c6fc899376b8
-- title:
--   Lemma 5.3 — a sparse random set T has |A+T| ≥ |A|(|T|−pn/4) for all A with |A| ≤ u, except with probability n^{−Ω(pn)}
-- statement:
--   Let $T\subseteq\{0,\dots,n-1\}$ be a random set that contains every element independently with probability $p$, and suppose that $pn\le n^{3/5}$ and that $pn$ is at least a sufficiently large absolute threshold $M\ge2$. Let $u$ be a positive integer with $u\le(pn)^{1/4}$. Then, except with probability at most $n^{-c\,pn}$, every set $A\subseteq\{0,\dots,n-1\}$ with $|A|\le u$ satisfies
--
--   $$|A+T|\ge|A|\,\bigl(|T|-pn/4\bigr),$$
--
--   where $A+T$ is the integer sumset and $c>0$, $M$ are absolute constants.
--
--   Applied to the live $y$-indices after two restrictions, this supplies the expansion hypothesis of Lemma 5.4.
--
--   Differences from the source:
--   - encoding: pn sufficiently large; probability n^{−Ω(pn)} → ∃ c > 0 and a threshold M ≥ 2, both chosen before n, p and u, with M ≤ pn and failure probability at most n^{−c·pn}; reason: the meaning of 'sufficiently large' and Ω with absolute constants
--   - encoding: a random set containing each element with probability p → the sum over all subsets T of {0,…,n−1} of p^{|T|}(1−p)^{n−|T|}, with 0 ≤ p ≤ 1; reason: the product law written out; p is a probability
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 5.3, printed p.17 (PDF p.19)

import Mathlib
open scoped Pointwise

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Lemma 5.3, printed p.17 / PDF 19. The probability is over the random set
`T ⊆ {0,…,n−1}` containing each element independently with probability `p`. -/
theorem lemma_5_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ M : ℝ, 2 ≤ M ∧ ∀ (n : ℕ) (p : ℝ) (u : ℕ),
      0 ≤ p → p ≤ 1 → M ≤ p * n → p * n ≤ (n : ℝ) ^ ((3 : ℝ) / 5) →
      1 ≤ u → (u : ℝ) ≤ (p * n) ^ ((1 : ℝ) / 4) →
      (∑ T ∈ (Finset.range n).powerset,
        p ^ T.card * (1 - p) ^ (n - T.card) *
          (if ∃ A ∈ (Finset.range n).powerset, A.card ≤ u ∧
              ((A + T).card : ℝ) < (A.card : ℝ) * ((T.card : ℝ) - p * n / 4)
            then (1 : ℝ) else 0)) ≤
        (n : ℝ) ^ (-(c * (p * n))) := by sorry

end ParityBarrier563.Trilinear
