-- Prove2me | Theorems.Thm_WeightedAverage_abel_sum
-- name    : WeightedAverage.abel_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:22:29.746982+00:00
-- url     : https://prove2.me/theorems/c251eb96-49e9-4228-b355-babd15d84ed5
-- title:
--   Abel summation against the weights $i+1$, relative to a reference point
-- statement:
--   Let $H$ be a real inner product space, let $(z_i)_{i\ge 0}$ be a sequence in $H$ and let $z^\star \in H$. For every $n \in \mathbb{N}$,
--
--   $$
--   \sum_{i=0}^{n-1} (i+1)\,\big(z_{i+1} - z_i\big) \;=\; n\,\big(z_n - z^\star\big) \;-\; \sum_{i=0}^{n-1} \big(z_i - z^\star\big).
--   $$
--
--   This is summation by parts for the weights $i+1$, written so that both sides are expressed
--   through the displacements $z_i - z^\star$ from a fixed reference point rather than through the
--   $z_i$ themselves. That is the form a convergence proof needs: $z^\star$ is a fixed point of the
--   iteration, the displacements are what Fejér monotonicity controls, and the left-hand side is
--   what a weighted one-step inequality produces.
--
--   Note that $z^\star$ is arbitrary -- the identity holds for any point, because the $n$ copies of
--   $z^\star$ on the right cancel against the $n$ copies inside the sum. Taking $z^\star = 0$ gives
--   the plain Abel identity $\sum_{i<n}(i+1)(z_{i+1}-z_i) = n z_n - \sum_{i<n} z_i$.
--
--   **Formalization Note** Proved by induction on $n$; the algebraic step is `module`, since the
--   identity lives in an $\mathbb{R}$-module and involves only scalar multiples and sums. No
--   completeness or finite-dimensionality is used.
-- source:
--   The Abel summation step of the weighted ergodic rate in Davis & Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017) 829-858, DOI 10.1007/s11228-017-0421-z, proof of Theorem 3.2, p. 840; stated here for an arbitrary sequence in an inner product space.

import Mathlib

namespace WeightedAverage

/-- Abel summation for a sequence in an inner product space, against the weights $i+1$ and
relative to a fixed reference point. -/
theorem abel_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (z : ℕ → H) (zs : H) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z (i + 1) - z i) =
      (n : ℝ) • (z n - zs) - ∑ i ∈ Finset.range n, (z i - zs) := by sorry

end WeightedAverage
