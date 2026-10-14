-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_simon_linearIndependent_prob
-- name    : QAlgorithms.Nannicini.simon_linearIndependent_prob
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:43:53.677737+00:00
-- url     : https://prove2.me/theorems/b17d2698-8424-4602-a68d-abbe79f0968c
-- title:
--   Simon's algorithm: n+t uniform samples orthogonal to a contain n−1 independent vectors with probability ≥ 1 − 2^{−(t+1)}
-- statement:
--   This is the sampling bound behind the classical post-processing of Simon's algorithm.
--
--   Let $n \ge 1$ and $t \ge 0$ be integers, and let $\mathbb F_2 = \{0,1\}$ be the field with two elements. Fix a nonzero vector $a \in \mathbb F_2^n$ and let
--
--   $$V_a = \{k \in \mathbb F_2^n : k \cdot a = \textstyle\sum_{i=1}^n k_i a_i \equiv 0 \pmod 2\}$$
--
--   be the $(n-1)$-dimensional subspace of vectors orthogonal to $a$. Draw $k^{(1)}, \dots, k^{(n+t)}$ independently and uniformly at random from $V_a$. Then
--
--   $$\Pr\big[\text{some } n-1 \text{ of } k^{(1)}, \dots, k^{(n+t)} \text{ are linearly independent over } \mathbb F_2\big] \ge 1 - \frac{1}{2^{t+1}}.$$
--
--   The bound does not depend on $n$, so $n + O(1)$ runs of Simon's circuit suffice to determine the hidden string $a$ with high probability.
--
--   **Formalization Note** The probability is the fraction of all $|V_a|^{n+t}$ tuples $(k^{(1)},\dots,k^{(n+t)}) \in V_a^{n+t}$ for which there are $n-1$ distinct indices whose vectors are linearly independent; vectors of $\mathbb F_2^n$ are functions $\mathrm{Fin}\,n \to \mathbb Z/2\mathbb Z$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 51, Proposition 2.8. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Basic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms

open Classical in
/-- Nannicini p.51, Proposition 2.8: let `a ∈ 𝔽₂ⁿ` be nonzero, so that the vectors orthogonal to
`a` (`k ⬝ᵥ a = 0` in `𝔽₂`) form a subspace `V_a` of dimension `n − 1`. If `k⁽¹⁾, …, k⁽ⁿ⁺ᵗ⁾` are
drawn independently and uniformly at random from `V_a`, then the probability that among them
there are `n − 1` linearly independent vectors (over `𝔽₂`) is at least `1 − 1/2^{t+1}`.

The probability is the fraction of the `|V_a|^{n+t}` equally likely tuples `k : Fin (n+t) → V_a`
for which some `n − 1` distinct indices carry linearly independent vectors. -/
theorem simon_linearIndependent_prob (n t : ℕ) (a : Fin n → ZMod 2) (ha : a ≠ 0) :
    (Fintype.card {k : Fin (n + t) → {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0} //
        ∃ s : Fin (n - 1) ↪ Fin (n + t),
          LinearIndependent (ZMod 2) (fun i => ((k (s i) : {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0}) :
            Fin n → ZMod 2))} : ℝ) /
      (Fintype.card (Fin (n + t) → {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0}) : ℝ) ≥
      1 - 1 / 2 ^ (t + 1) := by sorry

end QAlgorithms.Nannicini
